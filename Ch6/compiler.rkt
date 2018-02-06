#lang racket
(require racket/match)
(require racket/set)
(require "utilities.rkt")
(require "interp.rkt")

(provide
  typecheck uniquify
  expose-allocation reveal-functions
  flatten select-instructions uncover-live
  build-interference allocate-registers
  ; assign-homes
  lower-conditionals
  patch-instructions print-x86
  r4-passes r4-passes-dev r4-passes-e)

; input:  (program exp)
; output: (program (type type) exp)
(define (typecheck p) ((typecheck-r `()) p))

(define (typecheck-r env)
  (lambda (e)
    (println (format "top-exp: ~v" e))
    (define recur (typecheck-r env))
    (match e
      [(? fixnum?) (values `(has-type ,e Integer) `Integer)]
      [(? boolean?) (values `(has-type ,e Boolean) `Boolean)]
      [(? symbol?)
        ; (define symbol-T (lookup e env))
        (values
          `(has-type ,e ,(lookup e env))
          (lookup e env))]
          ; (if (list? symbol-T) (car symbol-T) symbol-T))]
      [`(let ([,x ,(app recur let_e let_T)]) ,body)
        (define new-env (cons (cons x let_T) env))
        (define-values (body_e body_T) ((typecheck-r new-env) body))
        (values
          `(has-type (let ([,x ,let_e]) ,body_e) ,body_T)
          body_T)]
      [`(define (,f ,params ...) : ,r ,body)
        (define new-env
          (let new-env-loop ([new-env env] [p-list params])
            (if (empty? p-list)
                new-env
                (match (car p-list)
                  [`(,p : ,p-type)
                    (new-env-loop
                      (cons (cons p p-type) new-env)
                      (cdr p-list))]
                    ))))
        (define-values (body_e body_T) ((typecheck-r new-env) body))
        (unless (equal? body_T r) 
          (error `typecheck-r "`define return type doesn't match body ~v" e))
        (values `(has-type (define (,f ,@params) : ,r ,body_e) (,@(map caddr params) -> ,r)) `(,@(map cddr params) -> ,r))]
      [`(if ,(app recur cnd_e cnd_T)
            ,(app recur thn_e thn_T)
            ,(app recur els_e els_T))
        (unless (type-boolean cnd_T)
          (error `typecheck-r "`if` expected a Boolean condition ~v" e))
        (define if_e `(if ,cnd_e ,thn_e ,els_e))
        (if (equal? thn_T els_T)
            (values `(has-type ,if_e ,thn_T) thn_T)
            (error `typecheck-r "`if` branches must return same type ~v" e))]
      [`(not ,(app recur not_e not_T))
        (if (type-boolean not_T)
            (values `(has-type (not ,not_e) Boolean) `Boolean)
            (error `typecheck-r "`not` expected a Boolean ~v" e))]
      [`(and ,(app recur e1 T1) ,(app recur e2 T2))
        (if (and (type-boolean T1) (type-boolean T2))
            (values `(has-type (and ,e1 ,e2) Boolean) `Boolean)
            (error `typecheck-r "`and` expected a Boolean ~v" e))]
      [`(void) (values `(has-type (void) Void) `Void)]
      [`(vector ,(app recur e* t*) ...)
        (let ([t `(Vector ,@t*)])
          (values `(has-type (vector ,@e*) ,t) t))]
      [`(vector-ref ,(app recur e t) ,i)
        (match t
          [`(Vector ,ts ...)
            (unless (and (exact-nonnegative-integer? i)
                          (i . < . (length ts)))
              (error `typecheck-r "invalid index ~a" i))
            (let ([t (list-ref ts i)])
                  (values
                    `(has-type (vector-ref ,e (has-type ,i Integer)) ,t)
                    t))]
          [else (error `typecheck-r
                       "expected a vector in vector-ref, not ~v" t)])]
      [`(vector-set! ,(app recur e-vec^ t-vec)
                     ,i
                     ,(app recur e-arg^ t-arg))
        (match t-vec
          [`(Vector ,ts ...)
            (unless (and (exact-nonnegative-integer? i)
                         (i . < . (length ts)))
              (error `typecheck-r "invalid index ~a" i))
            (unless (equal? (list-ref ts i) t-arg)
              (error `typecheck-r "type mismatch in vector-set! ~a ~a"
                (list-ref ts i) t-arg))
            (values `(has-type (vector-set! ,e-vec^
                                (has-type ,i Integer)
                                ,e-arg^) Void) `Void)]
          [else (error `typecheck-r
                  "expected a vector in vector-set!, not ~a" t-vec)])]
      [`(eq? ,(app recur e1 T1) ,(app recur e2 T2))
        (if (equal? T1 T2)
            (values `(has-type (eq? ,e1 ,e2) Boolean) `Boolean)
            (error
              `typecheck-r
              "`eq?` nonequal argument types ~v" e))]
      [`(< ,(app recur e1 T1) ,(app recur e2 T2))
        (if (and (type-integer T1) (type-integer T2))
            (values `(has-type (< ,e1 ,e2) Boolean) `Boolean)
            (error `typecheck-r "`<` expected Integer arguments ~v" e))]
      [`(<= ,(app recur e1 T1) ,(app recur e2 T2))
        (if (and (type-integer T1) (type-integer T2))
            (values `(has-type (<= ,e1 ,e2) Boolean) `Boolean)
            (error `typecheck-r "`<=` expected Integer arguments ~v" e))]
      [`(> ,(app recur e1 T1) ,(app recur e2 T2))
        (if (and (type-integer T1) (type-integer T2))
            (values `(has-type (> ,e1 ,e2) Boolean) `Boolean)
            (error `typecheck-r "`>` expected Integer arguments ~v" e))]
      [`(>= ,(app recur e1 T1) ,(app recur e2 T2))
        (if (and (type-integer T1) (type-integer T2))
            (values `(has-type (>= ,e1 ,e2) Boolean) `Boolean)
            (error `typecheck-r "`>=` expected Integer arguments ~v" e))]
      [`(+ ,(app recur e1 T1) ,(app recur e2 T2))
        (if (and (type-integer T1) (type-integer T2))
            (values `(has-type (+ ,e1 ,e2) Integer) `Integer)
            (error `typecheck-r "`+` expected Integer arguments ~v" e))]
      [`(- ,(app recur e1 T1))
        (if (type-integer T1)
            (values `(has-type (- ,e1) Integer) `Integer)
            (error `typecheck-r "`-` expected Integer argument ~v" e))]
      [`(read) (values `(has-type (read) Integer) `Integer)]
      [`(program ,body ...)
        (let* ([my-defines (get-define-stmts body)]
               [my-stmts (list-tail body (length my-defines))]
               [my-env (map get-define-env my-defines)])
          (define-values
            (defines_e defines_T)
            (map2 (typecheck-r my-env) my-defines))
          (define-values
            (body_e body_T)
            (map2 (typecheck-r my-env) my-stmts))
          `(program
            (type ,(last body_T))
            (defines ,@defines_e)
            ,@body_e))]
      [`(,f ,args ...)
        ; (println (format "func-exp: ~v" e))
        ; (println (format "func-env: ~v" env))
        (define-values (args_e args_T) (map2 recur args))
        (define-values (f_e f_T) (recur f))
        (define f-types
          (reverse (cddr (reverse f_T))))
        (define f-return-type
          (last f_T))
        (unless (equal? args_T f-types)
          (error `typecheck-r
            "function ~v expected types ~v but received types ~v"
            f f-types args_T))
        (values
          `(has-type (,f_e ,@args_e) ,f-return-type)
          f-return-type)]
      )))


(define (get-define-stmts e)
  (filter (lambda (x)
    (match x
      [`(define (,f ,params ...) : ,r ,body) #t]
      [else #f]))
    e))

(define (get-define-env e)
  (match e
    [`(define (,f ,params ...) : ,r ,body)
      (cons f (append (map caddr params) (list `-> r)))]
    [else #f]))

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
        ; (println (format "e: ~v" e))
        ; (println (format "alist: ~v" alist))
        (let ([new-sym (assoc e alist)])
          (if new-sym (cadr new-sym) e))]
      [(? integer?) e]
      [(? boolean?) e]
      [`(let ([,x ,x-e]) ,body)
        ; (println (format "let-e: ~v" e))
        (let ([newSym (gensym x)])
          `(let ([,newSym ,((uniquify-r alist) x-e)])
              ,((uniquify-r (cons (list x newSym) alist)) body)))]
      [`(program (type ,t) (defines ,defines ...) ,e)
       `(program
          (type ,t)
          (defines ,@(map (uniquify-r alist) defines))
          ,((uniquify-r alist) e))]
      [`(defines ,stmts ...)
        `(defines ,@(map (uniquify-r alist) stmts))]
      [`(define (,f ,params ...) : ,r ,body)
        (let* ([new-syms (map gensym (map car params))]
               [unique-params (map
                (lambda (x y)
                  (list x (cadr y) (caddr y))) new-syms params)]
               [unique-body
                ((uniquify-r
                  (append
                    (map (lambda (x y) (list (car y) x)) new-syms params)
                    alist))
                  body)])
            `(define (,f ,@unique-params) : ,r ,unique-body)
          )]
      [`(has-type ,exp ,T)
        `(has-type ,((uniquify-r alist) exp) ,T)]
      [`(,op ,es ...)
       `(,((uniquify-r alist) op) ,@(map (uniquify-r alist) es))]
      [else (error `uniquify-r "uniquify-r couldn't match ~v" e)])))

; input:  (program (type type) (defines def*) exp)
; output: (program (type type) (defines def*) exp)
(define (reveal-functions e)
  ((reveal-functions-r (make-hash)) e))

(define (reveal-functions-r funcs)
  (lambda (e)
    (define recur (reveal-functions-r funcs))
    (match e
      [`(program (type ,type) (defines ,defines ...) ,exp)
        (map (lambda (d)
          (match d
            [`(has-type (define (,f ,_ ...) : ,_ ,_) ,type)
              (hash-set! funcs f type)]
            [else (error
              `reveal-functions "define statement not matched ~v" d)]))
          defines)
        `(program (type ,type)
          (defines
            ,@(map (reveal-functions-r funcs) defines))
          ,((reveal-functions-r funcs) exp))]
      [`(define (,f ,params ...) : ,r ,body)
        `(define (,f ,@params) : ,r ,(recur body))]
      [`(has-type ,exp ,T)
        `(has-type ,(recur exp) ,T)]
      [`(let ([,x ,e]) ,body)
        (define new-funcs (hash-copy funcs))
        (hash-set! new-funcs x (get-type e))
        `(let ([,x ,(recur e)])
          ; ,(recur body))]
          ,(if (is-func e)
            ((reveal-functions-r new-funcs) body)
            (recur body)))]
      [(? symbol?)
        (if (hash-has-key? funcs e )
            `(function-ref ,e)
            e)]
      [(? integer?) e]
      [(? boolean?) e]
      [`(,op ,args ...)
        (if (hash-has-key? funcs op)
          `(app
            (has-type (function-ref ,op) ,(hash-ref funcs op))
            ,@(map recur args))
          `(,op ,@(map recur args)))]
      [else (error `reveal-functions "invalid syntax ~v" e)]
  )))

(define (is-func e)
  (match e
    [`(has-type ,_ ,type)
      (not (not (member `-> type)))]))

(define (get-type e)
  (match e
    [`(has-type ,_ ,type) type]))

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
          [`(define (,f ,params ...) : ,r ,(app expose-allocation body))
            `(define (,f ,@params) : ,r ,body)]
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

    [`(program (type ,type) (defines ,defines ...) ,body)
      `(program
        (type ,type)
        (defines ,@(map expose-allocation defines))
        ,(expose-allocation body))]
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
    ; (println (format "line: ~v" e))
    (match e
      [`(program (type ,t) (defines ,defines ...) ,body)
        (define-values
          (e-flat e-assigns e-vars)
          ((flatten-r #t) body))
        `(program ,e-vars
          (type ,t)
          (defines ,@(map (flatten-r #t) defines))
          ,@e-assigns
          (return ,e-flat))]
      [(? symbol?) (values e `() `())]
      [`(has-type ,exp ,T)
        (match exp
          [(? symbol?) (values exp `() `())]
          [(? integer?) (values exp `() `())]
          [(? boolean?) (values exp `() `())]
          [`(define (,f ,params ...) : ,r ,body)
            (define-values
              (b-flat b-assigns b-vars)
              ((flatten-r use-temp) body))
            `(define (,f ,@params) : ,r ,b-vars ,@b-assigns (return ,b-flat))]
          [`(let ([,x ,v]) ,body)
            (match v
              [`(has-type ,v-exp ,v-type)
                (define-values
                  (v-flat v-assigns v-vars)
                  ((flatten-r #f) v))
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
              `((assign ,tmpSym ,exp))
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
            ; (println (format "op: ~v" op))
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
                      (cons (cons tmpSym T) es-vars)))]
                [else
                  (values
                    stmt
                    es-assigns
                    es-vars)]))])]
      [else (error `flatten-r "flatten could not match ~v" e)]
    )))

(define (op-return-type op)
  (match op
    [(or `+ `- `read `global-value) `Integer]
    [(or `eq? `< `<= `> `>= `not) `Boolean]
    [(or `vector-set! `void `collect) `Void]
    [else (error `op-return-type "op not recognized ~v" op)]))

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
        [`(function-ref ,f)
          `((leaq (function-ref ,f) (var ,var)))]
        [`(app ,f ,args ...)
          (let loop ([regs `(rdi rsi rdx rcx r8 r9)]
                     [params (cons `r15 args)]
                     [output `()]
                     [used-stack 0])
            (cond
              [(empty? params)
                (append output
                  `((indirect-callq (var ,f))
                    (movq (reg rax) (var ,var))))]
              [(empty? regs)
                (loop regs (cdr params)
                  (append output
                    `((movq ,(C1->x86 (car params)) (deref rsp ,(* 8 used-stack)))))
                  (+ 1 used-stack))]
              [else (loop
                (cdr regs)
                (cdr params)
                (append output
                  `((movq ,(C1->x86 (car params)) (reg ,(car regs)))))
                used-stack)]))]
      )]
    [`(define (,f ,params ...) : ,r ,vars ,body ...)
      `(define (,f) ,(+ 1 (length params))
        ,(list (append (map car params) (map car vars))
          (let ([p-length (length params)])
            (if (> p-length 6)
                (- p-length 5)
                0)))
        ,@(mov-args-to-vars (cons `r15 (map car params)) `(rdi rsi rdx rcx r8 r9) 0)
        ,@(append* (map select-instructions body)))]
    [`(return ,arg)
      (define a (C1->x86 arg))
      `((movq ,a (reg rax)))]
    [`(if (eq? ,e1 ,e2) ,thn ,els)
      `((if (eq? ,(C1->x86 e1) ,(C1->x86 e2))
           ,@(list (append* (map select-instructions thn)))
           ,@(list (append* (map select-instructions els)))))]
    [`(program ,vars
        (type ,t)
        (defines ,defines ...)
        ,body ...)
      `(program ,(map car vars)
        (type ,t)
        (defines ,@(map select-instructions defines))
        ,@(append* (map select-instructions body)))]
    ))

(define (mov-args-to-vars vars regs used-stack)
  ; (println (format "vars: ~v" vars))
  (cond
    [(empty? vars) `()]
    [(empty? regs)
      (cons
        `(movq (deref rbp ,(* 8 used-stack)) ,(C1->x86 (car vars)))
        (mov-args-to-vars (cdr vars) regs (+ 1 used-stack)))]
    [else
      (cons
        `(movq (reg ,(car regs)) ,(C1->x86 (car vars)))
        (mov-args-to-vars (cdr vars) (cdr regs) used-stack))]))

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
    [(equal? d `r15) `(reg ,d)]
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
        (defines ,defines ...)
        ,body ...)
      (define-values
        (live-afters instructions)
        (live-vars (reverse body) (set)))
      `(program
        (,vars
         ,(cdr (reverse (cons `() live-afters))))
        (type ,type)
        (defines ,@(map uncover-live defines))
        ,@(reverse instructions))]
    [`(define (,f) ,num-params (,vars ,max-stack) ,body ...)
      (define-values
        (live-afters instructions)
        (live-vars (reverse body) (set)))
      `(define (,f)
        ,num-params
        (,vars ,(cdr (reverse (cons `() live-afters))) ,max-stack)
        ,@(reverse instructions))]
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
      [`(indirect-callq ,arg)
        (define new-live
          (add-live-vars arg #t current-live))
        (define-values (lives instructions) (live-vars (cdr e) new-live))
        (values
          (cons (set->list new-live) lives)
          (cons (car e) instructions))]
      [`(leaq (function-ref ,_) ,a2)
        (define new-live
          (add-live-vars a2 #f current-live))
        (define-values (lives instructions) (live-vars (cdr e) new-live))
        (values
          (cons (set->list new-live) lives)
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
    [`(program (,vars ,live-afters) (type ,type)
        (defines ,defines ...)
        ,body ...)
      (let ([graph (make-graph vars)])
        (map
          (lambda (i l) (build-interference-r i l graph))
          body
          live-afters)
        `(program
          (,vars ,graph)
          (type ,type)
          (defines ,@(map build-interference defines))
          ,@(remove-if-lives body)))]
    [`(define (,f) ,num-params (,vars ,live-afters ,max-stack) ,body ...)
      (let ([graph (make-graph vars)])
        (map
          (lambda (i l) (build-interference-r i l graph))
          body
          live-afters)
        `(define (,f) ,num-params
          (,vars ,graph ,max-stack)
          ,@(remove-if-lives body)))]
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
    [`(leaq ,_ ,a2)
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
    [`(indirect-callq ,_) "no graph changes needed"]
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
    [`(program (,var ,graph) (type ,type)
      (defines ,defines ...)
      ,body ...)
      (let ([color-map (color-graph graph var)]
            [m (make-hash)]
            [max-color 0])
        (map (lambda (v)
          (let ([color (hash-ref color-map v)])
            (cond
              [(equal? color 0) (hash-set! m v `(reg rbx))]
              [else (hash-set! m v (list `deref `rbp (* -8 color)))])
            (when (> color max-color)
              (set! max-color color))))
          var)
        `(program
          ,(* 8 max-color)
          (type ,type)
          (defines ,@(map allocate-registers defines))
          ,@(map (assign-homes-r m) body)))]
    [`(define (,f) ,num-params (,var ,graph ,max-stack) ,body ...)
      (let ([color-map (color-graph graph var)]
            [m (make-hash)]
            [max-color 0])
        (map (lambda (v)
          (let ([color (hash-ref color-map v)])
            (cond
              [(equal? color 0) (hash-set! m v `(reg rbx))]
              [else (hash-set! m v (list `deref `rbp (* -8 color)))])
            (when (> color max-color)
              (set! max-color color))))
          var)
        `(define (,f) 
          ,(* 8 max-color)
          ,@(map (assign-homes-r m) body)))]
    [else (error `allocate-registers "program has invalid syntax ~v" p)]))

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
      [`(function-ref ,_) e]
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
    [`(program ,stack-size (type ,type)
      (defines ,defines ...)
      ,body ...)
      `(program ,stack-size (type ,type)
        (defines ,@(map lower-conditionals defines))
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
    [`(define (,f) ,stack-size ,body ...)
      `(define (,f) ,stack-size
        ,@(append* (map lower-conditionals body)))]
    [else (list e)]
  ))

; input:  x86_1 -> (program stack-size (type type) instr+)
; output: x86_1 -> (program stack-size (type type) instr+)
(define (patch-instructions e)
  (define e-new (remove-double-stack-ref e))
  (if (not e-new)
      (match e
        [`(program ,size (type ,type)
            (defines ,defines ...) ,body ...)
          `(program ,size (type ,type)
            (defines ,@(map patch-instructions defines))
            ,@(append* (map patch-instructions body)))]
        [`(define (,f) ,stack-size ,body ...)
          `(define (,f) ,stack-size ,@(append* (map patch-instructions body)))]
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
        [`(leaq ,a1 ,a2)
          (match a2
            [`(deref ,reg ,offset)
              `((leaq ,a1 (reg rax))
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

(define (patch-func-bug p)
  (match p
    [`(program ,size (type ,type)
        (defines ,defines ...) ,body ...)
      ((patch-func-bug-r (list->set (map caadr defines))) p)]))

(define (patch-func-bug-r funcs)
  (lambda (e)
    (define recur (patch-func-bug-r funcs))
    (match e
      [`(program ,size (type ,type)
          (defines ,defines ...) ,body ...)
        `(program ,size (type ,type)
          (defines ,@(map recur defines))
          ,@(append* (map recur body)))]
      [`(define (,f) ,stack-size ,body ...)
        `(define (,f) ,stack-size ,@(append* (map recur body)))]
      [`(leaq (function-ref ,label) ,arg)
        (if (set-member? funcs label)
          (list e)
          `())]
      [else (list e)])))

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
    [`(program ,size (type ,type)
        (defines ,defines ...) ,body ...)
      (string-replace (string-append
        (string-join (map print-x86 defines) "\n\n")
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
        "\n"
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
        "    retq\n"
      ) "?" "question")]
    [`(define (,f) ,stack-size ,body ...)
      (string-append
        (format "    .globl ~a\n" f)
        (format "~a:\n" f)
        "    pushq   %rbp\n"
        "    pushq   %rbx\n"
        "    movq    %rsp, %rbp\n"
        (if (> stack-size 0)
          (format "    subq    $~v, %rsp\n" stack-size)
          "")
        "\n"
        (string-join (map print-x86 body) "\n") "\n"
        "\n"
        (if (> stack-size 0)
          (format "    addq    $~v, %rsp\n" stack-size)
          "")
        "    popq    %rbx\n"
        "    popq    %rbp\n"
        "    retq\n"
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
    [`(indirect-callq ,arg)
      (format "    callq   *~a" (print-x86 arg))]
    [`(leaq ,a1 ,a2)
      (format "    leaq    ~a, ~a" (print-x86 a1) (print-x86 a2))]

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
    [`(function-ref ,label)
      (format "~a(%rip)" label)]
    [else (error `print-x86 "invalid grammar ~v" e)]
  ))

(define r4-passes
  `(
     ; ("typecheck" ,typecheck #f)
     ("uniquify" ,uniquify ,interp-scheme)
     ("reveal-functions" ,reveal-functions ,interp-scheme)
     ; ("expose-allocation" ,expose-allocation ,interp-scheme)
     ("flatten" ,flatten ,interp-C)
     ("select-instructions" ,select-instructions ,interp-x86)
     ("uncover-live" ,uncover-live ,interp-x86)
     ("build-interference" ,build-interference ,interp-x86)
     ("allocate-registers" ,allocate-registers ,interp-x86)
     ; ; ("assign-homes" ,assign-homes ,interp-x86)
     ("lower-conditionals" ,lower-conditionals ,interp-x86)
     ("patch-instructions" ,patch-instructions ,interp-x86)
     ("patch-func-bug" ,patch-func-bug ,interp-x86)
     ("print-x86" ,print-x86 #f)
  ))

(define (r4-passes-dev p)
  (select-instructions
  (flatten
  (reveal-functions
  (uniquify
  (typecheck
  p))))))

(define (r4-passes-e p)
  ; (flatten
  (reveal-functions
  (uniquify
  (typecheck
  p))))