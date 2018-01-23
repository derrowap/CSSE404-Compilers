#lang racket
(require racket/match)
(require racket/set)
(require "utilities.rkt")
(require "interp.rkt")

(provide
  typecheck uniquify
  expose-allocation
  flatten select-instructions uncover-live
  build-interference allocate-registers
  ; assign-homes
  lower-conditionals
  patch-instructions print-x86 r3-passes)

; input:  (program exp)
; output: (program (type type) exp)
(define (typecheck p) ((typecheck-R3 `()) p))

(define (typecheck-R3 env)
  (lambda (e)
    (define recur (typecheck-R3 env))
    (match e
      [(? fixnum?) (values `(has-type ,e Integer) `Integer)]
      [(? boolean?) (values `(has-type ,e Boolean) `Boolean)]
      [(? symbol?) (values `(has-type ,e ,(lookup e env)) (lookup e env))]
      [`(let ([,x ,(app recur let_e let_T)]) ,body)
        (define new-env (cons (cons x let_T) env))
        (define-values (body_e body_T) ((typecheck-R3 new-env) body))
        (values
          `(has-type (let ([,x ,let_e]) ,body_e) ,body_T)
          body_T)]
      [`(if ,(app recur cnd_e cnd_T)
            ,(app recur thn_e thn_T)
            ,(app recur els_e els_T))
        (unless (type-boolean cnd_T)
          (error `typecheck-R3 "`if` expected a Boolean condition ~v" e))
        (define if_e `(if ,cnd_e ,thn_e ,els_e))
        (if (equal? thn_T els_T)
            (values `(has-type ,if_e ,thn_T) thn_T)
            (error `typecheck-R3 "`if` branches must return same type ~v" e))]
      [`(not ,(app recur not_e not_T))
        (if (type-boolean not_T)
            (values `(has-type (not ,not_e) Boolean) `Boolean)
            (error `typecheck-R3 "`not` expected a Boolean ~v" e))]
      [`(and ,(app recur e1 T1) ,(app recur e2 T2))
        (if (and (type-boolean T1) (type-boolean T2))
            (values `(has-type (and ,e1 ,e2) Boolean) `Boolean)
            (error `typecheck-R3 "`and` expected a Boolean ~v" e))]
      [`(void) (values `(has-type (void) Void) `Void)]
      [`(vector ,(app recur e* t*) ...)
        (let ([t `(Vector ,@t*)])
          (values `(has-type (vector ,@e*) ,t) t))]
      [`(vector-ref ,(app recur e t) ,i)
        (match t
          [`(Vector ,ts ...)
            (unless (and (exact-nonnegative-integer? i)
                          (i . < . (length ts)))
              (error `typecheck-R3 "invalid index ~a" i))
            (let ([t (list-ref ts i)])
                  (values
                    `(has-type (vector-ref ,e (has-type ,i Integer)) ,t)
                    t))]
          [else (error "expected a vector in vector-ref, not" t)])]
      [`(vector-set! ,(app recur e-vec^ t-vec)
                     ,i
                     ,(app recur e-arg^ t-arg))
        (match t-vec
          [`(Vector ,ts ...)
            (unless (and (exact-nonnegative-integer? i)
                         (i . < . (length ts)))
              (error `typecheck-R3 "invalid index ~a" i))
            (unless (equal? (list-ref ts i) t-arg)
              (error `typecheck-R3 "type mismatch in vector-set! ~a ~a"
                (list-ref ts i) t-arg))
            (values `(has-type (vector-set! ,e-vec^
                                (has-type ,i Integer)
                                ,e-arg^) Void) `Void)]
          [else (error `typecheck-R3
                  "expected a vector in vector-set!, not ~a" t-vec)])]
      [`(eq? ,(app recur e1 T1) ,(app recur e2 T2))
        (if (equal? T1 T2)
            (values `(has-type (eq? ,e1 ,e2) Boolean) `Boolean)
            (error
              `typecheck-R3
              "`eq?` nonequal argument types ~v" e))]
      [`(< ,(app recur e1 T1) ,(app recur e2 T2))
        (if (and (type-integer T1) (type-integer T2))
            (values `(has-type (< ,e1 ,e2) Boolean) `Boolean)
            (error `typecheck-R3 "`<` expected Integer arguments ~v" e))]
      [`(<= ,(app recur e1 T1) ,(app recur e2 T2))
        (if (and (type-integer T1) (type-integer T2))
            (values `(has-type (<= ,e1 ,e2) Boolean) `Boolean)
            (error `typecheck-R3 "`<=` expected Integer arguments ~v" e))]
      [`(> ,(app recur e1 T1) ,(app recur e2 T2))
        (if (and (type-integer T1) (type-integer T2))
            (values `(has-type (> ,e1 ,e2) Boolean) `Boolean)
            (error `typecheck-R3 "`>` expected Integer arguments ~v" e))]
      [`(>= ,(app recur e1 T1) ,(app recur e2 T2))
        (if (and (type-integer T1) (type-integer T2))
            (values `(has-type (>= ,e1 ,e2) Boolean) `Boolean)
            (error `typecheck-R3 "`>=` expected Integer arguments ~v" e))]
      [`(+ ,(app recur e1 T1) ,(app recur e2 T2))
        (if (and (type-integer T1) (type-integer T2))
            (values `(has-type (+ ,e1 ,e2) Integer) `Integer)
            (error `typecheck-R3 "`+` expected Integer arguments ~v" e))]
      [`(- ,(app recur e1 T1))
        (if (type-integer T1)
            (values `(has-type (- ,e1) Integer) `Integer)
            (error `typecheck-R3 "`-` expected Integer argument ~v" e))]
      [`(read) (values `(has-type (read) Integer) `Integer)]
      [`(program ,body)
        (define-values (body_e body_T) ((typecheck-R3 `()) body))
        `(program (type ,body_T) ,body_e)]
      )))

(define (type-boolean T)
  (match T
    [`Boolean #t]
    [else #f]))

(define (type-integer T)
  (match T
    [`Integer #t]
    [else #f]))

; input:  (program (type type) exp)
; output: (program (type type) exp)
(define (uniquify p)
  ((uniquify-r '()) p))

(define (uniquify-r alist)
  (lambda (e)
    (match e
      [(? symbol?)
       (let ([filtered (filter (lambda (x) (equal? (car x) e)) alist)])
        (if (empty? filtered)
            (gensym e)
            (cadar filtered)))]
      [(? integer?) e]
      [(? boolean?) e]
      [`(let ([,x ,e]) ,body)
        (let ([newSym (gensym x)])
          `(let ([,newSym ,((uniquify-r alist) e)])
              ,((uniquify-r (cons (list x newSym) alist)) body)))]
      [`(program (type ,t) ,e)
       `(program
          (type ,t)
          ,((uniquify-r alist) e))]
      [`(has-type ,exp ,T)
        `(has-type ,((uniquify-r alist) exp) ,T)]
      [`(,op ,es ...)
       `(,op ,@(map (uniquify-r alist) es))]
      [else (error `uniquify-r "uniquify-r couldn't match ~v" e)])))

; input:  (program (type type) exp)
; output: (program (type type) exp)
(define (expose-allocation e)
  (match e
    [`(has-type ,exp ,T)
      (list `has-type
        (match exp
          [(? fixnum?) exp]
          [(? boolean?) exp]
          [(? symbol?) exp]
          [`(void) exp]
          [`(vector ,(app expose-allocation e_n) ...)
            (define v_sym (gensym `v))
            (cond
              [(empty? e_n)
              `(has-type
                (let ([_ (has-type
                  (if (has-type
                    (< (has-type
                      (+ (has-type
                        (global-value free_ptr)
                        Integer)
                        (has-type 8 Integer))
                      Integer)
                      (has-type
                        (global-value fromspace_end)
                        Integer))
                    Boolean)
                    (has-type (void) Void)
                    (has-type (collect 8) Void))
                  Void)])
                  (has-type
                    (let ([,v_sym (has-type
                      (allocate 0 ,T)
                      ,T)])
                      (has-type ,v_sym ,T))
                    Void))
                Void)]
              [else
                (define vm (vector-var-mapping e_n))
                (define bytes (+ 8 (* 8 (length e_n))))
                (define space-check
                  `(has-type
                    (let ([_ (has-type
                      (if (has-type
                            (< (has-type
                                (+ (has-type
                                    (global-value free_ptr)
                                    Integer)
                                   (has-type ,bytes Integer))
                                Integer)
                              (has-type (global-value fromspace_end) Integer))
                            Boolean)
                        (has-type (void) Void)
                        (has-type (collect (has-type ,bytes Integer)) Void))
                        Void)])
                      (has-type
                        (let ([,v_sym 
                          (has-type
                            (allocate
                              ,(length e_n)
                              ,T) ; wrap type in a has-type ???
                            ,T)])
                        ,(vector-set-lets vm e_n v_sym T))
                        Void))
                    Void))
                (mapping-to-lets vm e_n space-check)])]
          [`(let ([,x ,(app expose-allocation let_e)])
              ,(app expose-allocation body_e))
            `(let ([,x ,let_e]) ,body_e)]
          [`(if ,(app expose-allocation cnd_e)
                ,(app expose-allocation thn_e)
                ,(app expose-allocation els_e))
            `(if ,cnd_e ,thn_e ,els_e)]
          [`(read) `(read)]
          [`(,op ,(app expose-allocation a1)
                 ,(app expose-allocation a2)
                 ,(app expose-allocation a3))
            `(,op ,a1 ,a2 ,a3)]
          [`(,op ,(app expose-allocation arg1) ,(app expose-allocation arg2))
            `(,op ,arg1 ,arg2)]
          [`(,op ,(app expose-allocation arg))
            `(,op ,arg)]
          [else (error `expose-allocation "invalid exp syntax ~v" exp)])
        T)]
    [`(program (type ,type) ,body ...)
      `(program (type ,type) ,@(map expose-allocation body))]
    [else (error `expose-allocation "invalid syntax ~v" e)]))

(define (vector-var-mapping vals)
  (define m (make-hash))
  (map (lambda (v) (hash-set! m v (gensym `x))) vals)
  m)

(define (mapping-to-lets m vals body)
  (define vals-r (reverse vals))
  (let f ([output `(let ([,(hash-ref m (car vals-r)) ,(car vals-r)]) ,body)]
          [v (cdr vals-r)])
    (if (empty? v)
        output
        (f (list
            `let
            `([,(hash-ref m (car v)) ,(car v)])
            output)
          (cdr v)))))

(define (vector-set-lets m vals v_sym T)
  (define vals-r (reverse vals))
  (let f ([output
            `(has-type
              (let ([_ (has-type (vector-set!
                (has-type ,v_sym ,T)
                (has-type ,(- (length vals) 1) Integer)
                (has-type ,(hash-ref m (car vals-r)) (last T))) Void)])
                (has-type ,v_sym ,T))
              Void)]
          [v (cdr vals-r)]
          [n (- (length vals) 2)]
          [types (cdr (reverse (cdr T)))])
    (if (empty? v)
      output
      (f `(has-type (let
        ([_ (has-type (vector-set!
            (has-type ,v_sym ,T)
            (has-type ,n Integer)
            (has-type ,(hash-ref m (car v)) (car types))) Void)])
          ,output) Void)
        (cdr v)
        (- n 1)
        (cdr types)))))

; input:  (program (type type) exp)
; output: (program ([(var . type)|(var Vector type*)]*) (type type) stmt+)
(define (flatten p)
  ((flatten-r #f) p))

(define (flatten-r use-temp)
  (lambda (e)
    (match e
      [`(program (type ,t) ,body)
        (define-values
          (e-flat e-assigns e-vars)
          ((flatten-r #t) body))
        (append
          `(program ,e-vars (type ,t))
          (append e-assigns `((return ,e-flat))))]
      [`(has-type ,exp ,T) ((flatten-r use-temp) exp)]
      [(? symbol?) (values e `() `())]
      [(? integer?) (values e `() `())]
      [(? boolean?) (values e `() `())]
      [`(let ([,x ,v]) ,body)
        (match v
          [`(has-type ,v-exp ,v-type)
            (define-values
              (v-flat v-assigns v-vars)
              ((flatten-r #f) v-exp))
            (define-values
              (body-flat body-assigns body-vars)
              ((flatten-r use-temp) body))
            (values
              body-flat
              (append v-assigns `((assign ,x ,v-flat)) body-assigns)
              (append v-vars (list (cons x v-type)) body-vars))])]
      [`(if ,cnd ,thn ,els)
        (define-values
          (cnd-flat cnd-assigns cnd-vars)
          ((flatten-r #t) cnd))
        (define-values
          (thn-flat thn-assigns thn-vars)
          ((flatten-r #t) thn))
        (define-values
          (els-flat els-assigns els-vars)
          ((flatten-r #t) els))
        (define if-type
          (match thn
            [`(has-type ,_ ,type) type]))
        (let ([if-var (gensym `if)])
          (values
            if-var
            (append cnd-assigns (list
              (list `if (list `eq? #t cnd-flat)
                (append
                  thn-assigns
                  (list (list `assign if-var thn-flat)))
                (append
                  els-assigns
                  (list (list `assign if-var els-flat))))))
            (append cnd-vars (list (cons if-var if-type)) thn-vars els-vars)))]
      [`(and ,e1 ,e2)
        (define-values
          (e1-flat e1-assigns e1-vars)
          ((flatten-r #t) e1))
        (define-values
          (e2-flat e2-assigns e2-vars)
          ((flatten-r #t) e2))
        (define if-var (gensym `if))
        (values
          if-var
          (append e1-assigns (list
            (list `if (list `eq? #t e1-flat)
              (append
                e2-assigns
                (list (list `assign if-var e2-flat)))
              (list (list `assign if-var #f)))))
          (append e1-vars (list (cons if-var `Boolean)) e2-vars)
        )]
      [`(allocate ,size ,type)
        (define tmpSym (gensym `tmp))
        (values
          tmpSym
          `((assign ,tmpSym ,e))
          (list (cons tmpSym type)))]
      [`(vector-ref ,arg ,i-has-type)
        (match arg
          [`(has-type ,arg-exp ,arg-type)
            (define-values
              (arg-flat arg-assigns arg-vars)
              ((flatten-r #t) arg-exp))
            (define tmpSym (gensym `tmp))
            (define i
              (match i-has-type
                [`(has-type ,num ,_) num]))
            (define stmt `(vector-ref ,arg-flat ,i))
            (define stmt-type (list-ref arg-type (+ i 1)))
            (values
              tmpSym
              (append arg-assigns `((assign ,tmpSym ,stmt)))
              (cons (cons tmpSym stmt-type) arg-vars))
            ])]
      [`(,op ,es ...)
        (define-values
          (es-flat es-assigns-list es-vars-list)
          (map3 (flatten-r #t) es))
        (let ([es-assigns (append* es-assigns-list)]
              [es-vars (append* es-vars-list)]
              [stmt (cons op es-flat)])
          (cond
            [use-temp
              (let ([tmpSym (gensym `tmp)])
                (values
                  tmpSym
                  (append es-assigns `((assign ,tmpSym ,stmt)))
                  (cons (cons tmpSym (op-return-type op)) es-vars)))]
            [else
              (values
                stmt
                es-assigns
                es-vars)]))]
      [else (error `flatten-r "flatten could not match ~v" e)]
    )))

(define (op-return-type op)
  (match op
    [(or `+ `- `read `global-value) `Integer]
    [(or `eq? `< `<= `> `>= `not) `Boolean]
    [(or `vector-set! `void `collect) `Void]))

; input:  (program ([(var . type)|(var Vector type*)]*) (type type) stmt+)
; output: (program (var*) (type type) instr+)
(define (select-instructions e)
  (match e
    [`(assign ,var ,exp)
      (match exp
        [(? symbol?)
          (if (equal? var exp)
            `()
            `((movq (var ,exp) (var ,var))))]
        [(? integer?)
          `((movq (int ,exp) (var ,var)))]
        [(? boolean?)
          (if exp
              `((movq (int 1) (var ,var)))
              `((movq (int 0) (var ,var))))]
        [`(read)
          `((callq read_int)
            (movq (reg rax) (var ,var)))]
        [`(- ,arg)
          (define a (C1->x86 arg))
          `((movq ,a (var ,var))
            (negq (var ,var)))]
        [`(+ ,arg1 ,arg2)
          (define a1 (C1->x86 arg1))
          (define a2 (C1->x86 arg2))
          (cond
            [(equal? arg1 var)
              `((addq ,a2 (var ,var)))]
            [(equal? arg2 var)
              `((addq ,a1 (var ,var)))]
            [else
              `((movq ,a1 (var ,var))
                (addq ,a2 (var ,var)))])]
        [`(eq? ,arg1 ,arg2)
          (define a1 (C1->x86 arg1))
          (define a2 (C1->x86 arg2))
          `((cmpq ,a2 ,a1)
            (set e (byte-reg al))
            (movzbq (byte-reg al) (var ,var)))]
        [`(not ,arg)
          (define a (C1->x86 arg))
          `((movq ,a (var ,var))
            (xorq (int 1) (var ,var)))]
        [`(< ,arg1 ,arg2)
          (define a1 (C1->x86 arg1))
          (define a2 (C1->x86 arg2))
          `((cmpq ,a2 ,a1)
            (set l (byte-reg al))
            (movzbq (byte-reg al) (var ,var)))]
        [`(<= ,arg1 ,arg2)
          (define a1 (C1->x86 arg1))
          (define a2 (C1->x86 arg2))
          `((cmpq ,a2 ,a1)
            (set le (byte-reg al))
            (movzbq (byte-reg al) (var ,var)))]
        [`(> ,arg1 ,arg2)
          (define a1 (C1->x86 arg1))
          (define a2 (C1->x86 arg2))
          `((cmpq ,a2 ,a1)
            (set g (byte-reg al))
            (movzbq (byte-reg al) (var ,var)))]
        [`(>= ,arg1 ,arg2)
          (define a1 (C1->x86 arg1))
          (define a2 (C1->x86 arg2))
          `((cmpq ,a2 ,a1)
            (set ge (byte-reg al))
            (movzbq (byte-reg al) (var ,var)))]
        [`(vector-ref ,vec ,n)
          `((movq (var ,vec) (reg r11))
            (movq (deref r11 ,(* 8 (+ n 1))) (var ,var)))]
        [`(vector-set! ,vec ,n ,arg)
          `((movq (var ,vec) (reg r11))
            (movq ,(C1->x86 arg) (deref r11 ,(* 8 (+ n 1))))
            (movq (int 0) (var ,var)))]
        [`(allocate ,len (Vector ,types ...))
          (define tag (compute-tag len types))
          `((movq (global-value free_ptr) (var ,var))
            (addq (int ,(* 8 (+ len 1))) (global-value free_ptr))
            (movq (var ,var) (reg r11))
            (movq (int ,tag) (deref r11 0)))]
        [`(collect ,bytes)
          `((movq (reg r15) (reg rdi))
            (movq (int ,bytes) (reg rsi))
            (callq collect))]
        [`(void) `((movq (int 0) (var ,var)))]
        [`(global-value ,name) `((movq (global-value ,name) (var ,var)))]
      )]
    [`(return ,arg)
      (define a (C1->x86 arg))
      `((movq ,a (reg rax)))]
    [`(if (eq? ,e1 ,e2) ,thn ,els)
      `((if (eq? ,(C1->x86 e1) ,(C1->x86 e2))
           ,@(list (append* (map select-instructions thn)))
           ,@(list (append* (map select-instructions els)))))]
    [`(program ,vars
        (type ,t)
        ,body ...)
      `(program ,vars
        (type ,t)
        ,@(append* (map select-instructions body)))]
    ))

(define (compute-tag len types)
  ; (((0 + mask) << 6) + len) << 1
  (arithmetic-shift
    (+
      (arithmetic-shift
        (let mask-loop ([mask 0] [t types])
          (cond
            [(empty? t) mask]
            [(list? (car t))
              (mask-loop (+ 1 (arithmetic-shift mask 1)) (cdr t))]
            [else (mask-loop (arithmetic-shift mask 1) (cdr t))]))
        6)
      len)
    1))


(define (C1->x86 d)
  (cond
    [(symbol? d) `(var ,d)]
    [(integer? d) `(int ,d)]
    [(boolean? d)
      (if d `(int 1) `(int 0))]))

; intput: x86_1 -> (program (var*) (type type) instr+)
; output: x86_1 -> (program (var* live-afters) (type type) instr+)
(define (uncover-live p)
  (match p
    [`(program ,vars
        (type ,type)
        ,body ...)
      (define-values
        (live-afters instructions)
        (live-vars (reverse body) (set)))
      `(program
        ,@(append
            (list (list
              vars
              (append (cdr (reverse live-afters)) `(())))
              (list `type type))
            (reverse instructions)))]
    [else (error `uncover-live "invalid program received ~v" p)]
  ))

(define (live-vars e current-live)
  (if (empty? e)
    (values `() `())
    (match (car e)
      [`(if (eq? ,e1 ,e2) ,thn ,els)
        (define-values
          (live-before-thn thn-instructions)
          (live-vars (reverse thn) current-live))
        (define-values
          (live-before-els els-instructions)
          (live-vars (reverse els) current-live))
        (define live-before-if
          (set-union
            (list->set (last live-before-thn))
            (list->set (last live-before-els))))
        (define live-after-e1
          (add-live-vars e1 #t live-before-if))
        (define new-live
          (add-live-vars e2 #t live-after-e1))
        (define-values (lives instructions) (live-vars (cdr e) new-live))
        (values
          (cons (set->list new-live) lives)
          (cons
            `(if (eq? ,e1 ,e2)
                 ,@(list (reverse thn-instructions))
                 ,@(list (reverse live-before-thn))
                 ,@(list (reverse els-instructions))
                 ,@(list (reverse live-before-els)))
            instructions))]
      [`(movzbq ,a1 ,a2)
        (define live-after-a1
          (add-live-vars a1 #t current-live))
        (define new-live
          (add-live-vars a2 #f live-after-a1))
        (define-values (lives instructions) (live-vars (cdr e) new-live))
        (values
          (cons (set->list new-live) lives)
          (cons (car e) instructions))]
      [`(movq ,a1 ,a2)
        (define live-after-a1
          (add-live-vars a1 #t current-live))
        (define new-live
          (add-live-vars a2 #f live-after-a1))
        (define-values (lives instructions) (live-vars (cdr e) new-live))
        (values
          (cons (set->list new-live) lives)
          (cons (car e) instructions))]
      [`(addq ,a1 ,a2)
        (define live-after-a1
          (add-live-vars a1 #t current-live))
        (define new-live
          (add-live-vars a2 #t live-after-a1))
        (define-values (lives instructions) (live-vars (cdr e) new-live))
        (values
          (cons (set->list new-live) lives)
          (cons (car e) instructions))]
      [`(xorq ,a1 ,a2)
        (define live-after-a1
          (add-live-vars a1 #t current-live))
        (define new-live
          (add-live-vars a2 #t live-after-a1))
        (define-values (lives instructions) (live-vars (cdr e) new-live))
        (values
          (cons (set->list new-live) lives)
          (cons (car e) instructions))]
      [`(negq ,arg)
        (define new-live
          (add-live-vars arg #t current-live))
        (define-values (lives instructions) (live-vars (cdr e) new-live))
        (values
          (cons (set->list new-live) lives)
          (cons (car e) instructions))]
      [`(cmpq ,a1 ,a2)
        (define live-after-a1
          (add-live-vars a1 #t current-live))
        (define new-live
          (add-live-vars a2 #t live-after-a1))
        (define-values (lives instructions) (live-vars (cdr e) new-live))
        (values
          (cons (set->list new-live) lives)
          (cons (car e) instructions))]
      [`(set ,cc ,arg)
        (define new-live
          (add-live-vars arg #f current-live))
        (define-values (lives instructions) (live-vars (cdr e) new-live))
        (values
          (cons (set->list new-live) lives)
          (cons (car e) instructions))]
      [`(callq ,_)
        (define-values (lives instructions) (live-vars (cdr e) current-live))
        (values
          (cons (set->list current-live) lives)
          (cons (car e) instructions))]
      [else (error `live-vars "instruction has invalid syntax ~v" (car e))]
  )))

(define (add-live-vars arg is-read current-live)
  (match arg
    [`(var ,v)
      (if is-read
          (set-add current-live v)
          (set-remove current-live v))]
    [`(reg ,_) current-live]
    [`(int ,_) current-live]
    [`(byte-reg ,_) current-live]
    [`(deref ,_ ,_) current-live]
    [`(global-value ,_) current-live]
    [else (error `add-live-vars "invalid argument syntax ~v" arg)]))

; input:  (program (var* live-afters) (type type) instr+)
; output: (program (var* graph) (type type) instr+)
(define (build-interference p)
  (match p
    [`(program (,vars ,live-afters) (type ,type) ,body ...)
      (let ([graph (make-graph (map car vars))])
        (map
          (lambda (i l) (build-interference-r i l graph))
          body
          live-afters)
        `(program
            ,@(append
                (list (list vars graph) (list `type type))
                (remove-if-lives body))))]
    [else (error "invalid program syntax" p)]))

(define (build-interference-r instr live-vars graph)
  (match instr
    [`(if (eq? ,e1 ,e2) ,thn ,lives-thn ,els ,lives-els)
      (map (lambda (i l) (build-interference-r i l graph)) thn lives-thn)
      (map (lambda (i l) (build-interference-r i l graph)) els lives-els)]
    [`(movq ,a1 ,a2)
      (let ([s (arg->var a1)] [d (arg->var a2)])
        (map (lambda (v)
          (unless (or (equal? v s) (equal? v d) (boolean? d))
            (add-edge graph d v)))
          live-vars))]
    [`(movzbq ,a1 ,a2)
      (let ([s (arg->var a1)] [d (arg->var a2)])
        (map (lambda (v)
          (unless (or (equal? v s) (equal? v d) (boolean? d))
            (add-edge graph d v)))
          live-vars))]
    [`(addq ,_ ,a2)
      (let ([d (arg->var a2)])
        (map (lambda (v)
          (unless (or (equal? v d) (boolean? d))
            (add-edge graph d v)))
          live-vars))]
    [`(subq ,_ ,a2)
      (let ([d (arg->var a2)])
        (map (lambda (v)
          (unless (or (equal? v d) (boolean? d))
            (add-edge graph d v)))
          live-vars))]
    [`(negq ,arg)
      (let ([d (arg->var arg)])
        (map (lambda (v)
          (unless (or (equal? v d) (boolean? d))
            (add-edge graph d v)))
          live-vars))]
    [`(xorq ,_ ,a2)
      (let ([d (arg->var a2)])
        (map (lambda (v)
          (unless (or (equal? v d) (boolean? d))
            (add-edge graph d v)))
          live-vars))]
    [`(cmpq ,_ ,_) "no graph changes needed"]
    [`(set ,_ ,_) "no graph changes needed"]
    [`(jmp ,_) "no graph changes needed"]
    [`(jmp-if ,_ ,_) "no graph changes needed"]
    [`(label ,_) "no graph changes needed"]
    [`(callq ,_) "no graph changes needed"]
    [else (error "invalid instruction syntax" instr)]))

(define (remove-if-lives body)
  (map (lambda (e)
    (match e
      [`(if ,cnd ,thn ,_ ,els ,_)
        `(if ,cnd ,@(list (remove-if-lives thn)) ,@(list (remove-if-lives els)))]
      [else e]))
    body))

(define (arg->var arg)
  (match arg
    [`(var ,v) v]
    [else #f]))

; input:  x86_1 -> (program (var* graph) (type type) instr+)
; output: x86_1 -> (program stack-size (type type) instr+)
(define (allocate-registers p)
  (match p
    [`(program (,var ,graph) (type ,type) ,body ...)
      ; (println var)
      (let ([color-map (color-graph graph (map car var))]
            [m (make-hash)]
            [max-color 0])
        (map (lambda (v)
          (let ([color (hash-ref color-map v)])
            (cond
              [(equal? color 0) (hash-set! m v `(reg rbx))]
              [else (hash-set! m v (list `deref `rbp (* -8 color)))])
              ; [(equal? color 0) (hash-set! m v `(reg rdx))]
              ; [(equal? color 1) (hash-set! m v `(reg rcx))]
              ; [(equal? color 2) (hash-set! m v `(reg rsi))]
              ; [(equal? color 3) (hash-set! m v `(reg rdi))]
              ; [(equal? color 4) (hash-set! m v `(reg r8))]
              ; [(equal? color 5) (hash-set! m v `(reg r9))]
              ; [(equal? color 6) (hash-set! m v `(reg r10))]
              ; [(equal? color 7) (hash-set! m v `(reg r11))]
              ; [else (hash-set! m v (list `deref `rbp (* -8 (- color 7))))])
            (when (> color max-color)
              (set! max-color color))))
          (map car var))
        (cons
          `program
          (cons
            ; (* 8 (if (< (- max-color 7) 0) 0 (- max-color 7)))
            (* 8 max-color)
            (cons `(type ,type)
              (map (assign-homes-r m) body)))))]
    [else (error "program has invalid syntax" p)]))

(define (color-graph g vars)
  (let f ([color (make-hash)] [saturation (make-hash)] [W vars])
    (if (empty? W)
      color
      (let* ([u (highest-saturation saturation W)]
             [u-color (lowest-available-color (hash-ref saturation u (set)))])
        (hash-set! color u u-color)
        (map (lambda (adj)
          (hash-set!
            saturation
            adj
            (set-add (hash-ref saturation adj (set)) u-color)))
          (set->list (adjacent g u)))
        (f color saturation (remove u W)))
    )))

(define (highest-saturation saturation vars)
  (let f ([best-v (car vars)]
          [best-saturation (set-count (hash-ref saturation (car vars) (set)))]
          [vars (cdr vars)])
    (cond
      [(empty? vars) best-v]
      [(> (set-count (hash-ref saturation (car vars) (set))) best-saturation)
        (f
          (car vars)
          (set-count (hash-ref saturation (car vars) (set)))
          (cdr vars))]
      [else (f best-v best-saturation (cdr vars))])))

(define (lowest-available-color saturation)
  (let f ([candidate 0])
    (if (set-member? saturation candidate)
      (f (+ candidate 1))
      candidate)))

; (define (assign-homes p)
;   (match p
;     [`(program ,vars ,body ...)
;       (let ([m (make-hash)] [location 0])
;         (map
;           (lambda (v)
;             (set! location (- location 8))
;             (hash-set! m v `(deref rbp ,location)))
;           vars)
;         (cons `program
;               (cons (* -1 location) (map (assign-homes-r m) body))))]
;     [else (error "invalid program" p)]))

(define (assign-homes-r m)
  (lambda (e)
    (match e
      ; args
      [`(int ,_) e]
      [`(var ,v) (hash-ref m v)]
      [`(reg ,_) e]
      [`(byte-reg ,_) e]
      [`(deref ,_ ,_) e]
      [`(global-value ,_) e]
      ; instr
      [`(set ,_ ,_) e]
      [`(callq ,_) e]
      [`(if (eq? ,e1 ,e2) ,thn ,els)
        `(if (eq? ,((assign-homes-r m) e1) ,((assign-homes-r m) e2))
            ,@(list (map (assign-homes-r m) thn))
            ,@(list (map (assign-homes-r m) els)))]
      [`(,op ,arg)
        `(,op ,((assign-homes-r m) arg))]
      [`(,op ,a1 ,a2)
        `(,op
          ,((assign-homes-r m) a1)
          ,((assign-homes-r m) a2))]
      [else (error `assign-homes-r "not valid grammar: ~v, ~v" e m)])))

; input:  x86_1 -> (program stack-size (type type) instr+)
; output: x86_1 -> (program stack-size (type type) instr+)
(define (lower-conditionals e)
  (match e
    [`(program ,stack-size (type ,type) ,body ...)
      `(program ,stack-size (type ,type)
        ,@(append* (map lower-conditionals body)))]
    [`(if (eq? ,arg1 ,arg2) ,thns ,elss)
      (define thenlabel (gensym `thenlabel))
      (define endlabel (gensym `endlabel))
      (append
        `((cmpq ,arg2 ,arg1)
          (jmp-if e ,thenlabel))
        (append* (map lower-conditionals elss))
        `((jmp ,endlabel)
          (label ,thenlabel))
        (append* (map lower-conditionals thns))
        `((label ,endlabel)))]
    [else (list e)]
  ))

; input:  x86_1 -> (program stack-size (type type) instr+)
; output: x86_1 -> (program stack-size (type type) instr+)
(define (patch-instructions e)
  (define e-new (remove-double-stack-ref e))
  (if (not e-new)
      (match e
        [`(program ,size (type ,type) ,body ...)
          (cons `program (cons size (cons `(type ,type)
            (append* (map patch-instructions body)))))]
        [`(movq ,a1 ,a2)
          (if (equal? a1 a2)
              (list)
              (list e))]
        [`(movzbq ,a1 ,a2)
          (match a2
            [`(deref ,reg ,offset)
              `((movzbq ,a1 (reg rax))
                (movq (reg rax) (deref ,reg ,offset)))]
            [else (list e)])]
        [`(cmpq ,a1 ,a2)
          (match a2
            [`(int ,num)
              `((movq (int ,num) (reg rax))
                (cmpq ,a1 (reg rax)))]
            [else (list e)])]
        [else (list e)])
      e-new))

(define (remove-double-stack-ref e)
  (match e
    [`(,op ,a1 ,a2)
      (if (and (stack-ref? a1) (stack-ref? a2))
          `((movq ,a1 (reg rax))
            (,op (reg rax) ,a2))
          #f)]
    [else #f]))

(define (stack-ref? arg)
  (match arg
    [`(deref ,_ ,_) #t]
    [`(global-value ,_) #t]
    [else #f]))

; input:  x86_1 -> (program stack-size (type type) instr+)
; output: x86
(define (print-x86 e)
  (match e
    [`(program ,size (type ,type) ,body ...)
      (string-append
        "    .globl main\n"
        "main:\n"
        (if (> size 0)
            (string-append
              "    pushq   %rbp\n"
              "    movq    %rsp, %rbp\n"
              "    subq    $" (format "~a" size) ", %rsp\n")
            "")
        "    pushq   %rbx\n"
        "    movq    $64, %rdi\n"
        "    movq    $512, %rsi\n"
        "    callq   initialize\n"
        "    movq    rootstack_begin(%rip), %r15\n"
        "    movq    $0, (%r15)\n"
        ; "    addq    $0, %r15\n"
        "\n    "
        (string-join (map print-x86 body) "\n") "\n"
        "\n"
        (print-by-type type)
        "    movq    $0, %rax\n"
        ; "    subq    $0, %r15\n"
        (if (> size 0)
            (string-append
              "    addq    $" (format "~a" size) ", %rsp\n"
              "    popq    %rbp\n")
            "")
        "    popq    %rbx\n"
        "    retq"
      )]

    ; instr
    [`(movq ,a1 ,a2)
      (format "    movq    ~a, ~a" (print-x86 a1) (print-x86 a2))]
    [`(addq ,a1 ,a2)
      (format "    addq    ~a, ~a" (print-x86 a1) (print-x86 a2))]
    [`(negq ,arg)
      (format "    negq    ~a" (print-x86 arg))]
    [`(xorq ,a1 ,a2)
      (format "    xorq    ~a, ~a" (print-x86 a1) (print-x86 a2))]
    [`(cmpq ,a1 ,a2)
      (format "    cmpq    ~a, ~a" (print-x86 a1) (print-x86 a2))]
    [`(set ,cc ,arg)
      (format "    set~a    ~a" cc (print-x86 arg))]
    [`(movzbq ,a1 ,a2)
      (format "    movzbq  ~a, ~a" (print-x86 a1) (print-x86 a2))]
    [`(jmp ,label)
      (format "    jmp     ~a" label)]
    [`(jmp-if ,cc ,label)
      (format "    j~a      ~a" cc label)]
    [`(label ,label)
      (format "~a:" label)]
    [`(callq ,label)
      (format "    callq   ~a" label)]

    ; args
    [`(int ,num)
      (format "$~a" num)]
    [`(reg ,r)
      (format "%~a" r)]
    [`(byte-reg ,r)
      (format "%~a" r)]
    [`(deref ,reg ,offset)
      (format "~a(%~a)" offset reg)]
    [`(global-value ,name)
      (format "~a(%rip)" name)]
    [else (error `print-x86 "invalid grammar ~v" e)]
  ))

(define r3-passes
  `(
     ; ("typecheck" ,typecheck ,interp-scheme)
     ("uniquify" ,uniquify ,interp-scheme)
     ("expose-allocation" ,expose-allocation ,interp-scheme)
     ("flatten" ,flatten ,interp-C)
     ("select-instructions" ,select-instructions ,interp-x86)
     ("uncover-live" ,uncover-live ,interp-x86)
     ("build-interference" ,build-interference ,interp-x86)
     ("allocate-registers" ,allocate-registers ,interp-x86)
     ; ("assign-homes" ,assign-homes ,interp-x86)
     ("lower-conditionals" ,lower-conditionals ,interp-x86)
     ("patch-instructions" ,patch-instructions ,interp-x86)
     ("print-x86" ,print-x86 #f)
  ))
