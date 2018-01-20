#lang racket
(require racket/match)
(require racket/set)
(require "utilities.rkt")
(require "interp.rkt")

(provide
  uniquify flatten select-instructions
  uncover-live build-interference allocate-registers
  ; assign-homes
  patch-instructions
  print-x86 r1-passes)

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
      [`(let ([,x ,e]) ,body)
        (let ([newSym (gensym x)])
          `(let ([,newSym ,((uniquify-r alist) e)])
              ,((uniquify-r (cons (list x newSym) alist)) body)))]
      [`(program ,e)
       `(program ,((uniquify-r alist) e))]
      [`(,op ,es ...)
       `(,op ,@(map (uniquify-r alist) es))]
      [else (error "uniquify-r couldn't match" e)])))

(define (flatten p)
  ((flatten-r #f) p))

(define (flatten-r use-temp)
  (lambda (e)
    (match e
      [(? symbol?) (values e '() '())]
      [(? integer?) (values e '() '())]
      [`(let ([,x ,v]) ,body)
        (define-values
          (v-flat v-assigns v-vars)
          ((flatten-r #f) v))
        (define-values
          (body-flat body-assigns body-vars)
          ((flatten-r use-temp) body))
        (values
          body-flat
          (append v-assigns `((assign ,x ,v-flat)) body-assigns)
          (append v-vars (list x) body-vars))]
      [`(program ,body)
        (define-values
          (e-flat e-assigns e-vars)
          ((flatten-r #t) body))
        (append
          `(program ,e-vars)
          (append e-assigns `((return ,e-flat))))]
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
                  (cons tmpSym es-vars)))]
            [else
              (values
                stmt
                es-assigns
                es-vars)]))]
      [else (error "flatten could not match" e)]
    )))

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
        [`(read)
          `((callq read_int)
            (movq (reg rax) (var ,var)))]
        [`(- ,arg)
          (if (symbol? arg)
              `((movq (var ,arg) (var ,var))
                (negq (var ,var)))
              `((movq (int ,arg) (var ,var))
                (negq (var ,var))))]
        [`(+ ,arg1 ,arg2)
          (cond
            [(equal? arg1 var)
              (if (symbol? arg2)
                  `((addq (var ,arg2) (var ,var)))
                  `((addq (int ,arg2) (var ,var))))]
            [(equal? arg2 var)
              (if (symbol? arg1)
                  `((addq (var ,arg1) (var ,var)))
                  `((addq (int ,arg1) (var ,var))))]
            [(and (symbol? arg1) (symbol? arg2))
              `((movq (var ,arg1) (var ,var))
                (addq (var ,arg2) (var ,var)))]
            [(and (symbol? arg1) (integer? arg2))
              `((movq (var ,arg1) (var ,var))
                (addq (int ,arg2) (var ,var)))]
            [(and (integer? arg1) (symbol? arg2))
              `((movq (int ,arg1) (var ,var))
                (addq (var ,arg2) (var ,var)))]
            [(and (integer? arg1) (integer? arg2))
              `((movq (int ,arg1) (var ,var))
                (addq (int ,arg2) (var ,var)))])])]
    [`(return ,arg)
      (if (symbol? arg)
        `((movq (var ,arg) (reg rax)))
        `((movq (int ,arg) (reg rax))))]
    [`(program ,vars ,body ...)
      `(program ,vars ,@(append* (map select-instructions body)))]
    ))

; input: (program (var*) instr+)
; output: (program (var* live-afters) instr+)
(define (uncover-live p)
  (match p
    [`(program ,vars ,body ...)
      `(program
        ,@(append
            (list (list
              vars
              (append (cdr (reverse (live-vars (reverse body) (set)))) `(()))))
            body))]
    [else (error "invalid program received" p)]
  ))

(define (live-vars e current-live)
  (if (empty? e)
    `()
    (match (car e)
      [`(movq ,a1 ,a2)
        (let ([live-after-a1
          (match a1
            [`(var ,v) (set-add current-live v)]
            [`(reg ,_) current-live]
            [`(int ,_) current-live]
            [else (error "movq arg1 has invalid syntax" (car e))]
          )])
          (let ([new-live
            (match a2
              [`(var ,v) (set-remove live-after-a1 v)]
              [`(reg ,_) live-after-a1]
              [else (error "movq arg2 has invalid syntax" (car e))]
            )])
            (cons (set->list new-live) (live-vars (cdr e) new-live))))]
      [`(addq ,a1 ,a2)
        (let ([live-after-a1
          (match a1
            [`(var ,v) (set-add current-live v)]
            [`(reg ,_) current-live]
            [`(int ,_) current-live]
            [else (error "addq arg1 has invalid syntax" (car e))]
          )])
          (let ([new-live
            (match a2
              [`(var ,v) (set-add live-after-a1 v)]
              [`(reg ,_) live-after-a1]
              [else (error "addq 2nd arg has invalid syntax" (car e))]
            )])
            (cons (set->list new-live) (live-vars (cdr e) new-live))))]
      [`(negq ,arg)
        (let ([new-live
          (match arg
            [`(var ,v) (set-add current-live v)]
            [`(reg ,_) current-live]
            [else (error "negq expects var or reg" (car e))]
          )])
          (cons (set->list new-live) (live-vars (cdr e) new-live)))]
      [`(callq ,_)
        (cons (set->list current-live) (live-vars (cdr e) current-live))]
      [else (error "instruction has invalid syntax" (car e))]
  )))

; input: (program (var* live-afters) instr+)
; output: (program (var* graph) instr+)
(define (build-interference p)
  (match p
    [`(program (,vars ,live-afters) ,body ...)
      (let ([graph (make-graph vars)])
        (map (lambda (instr live-vars)
          (match instr
            [`(movq ,a1 ,a2)
              (let ([s (arg->var a1)] [d (arg->var a2)])
                (map (lambda (v)
                  (unless (or (equal? v s) (equal? v d))
                    (add-edge graph d v)))
                  live-vars))]
            [`(addq ,_ ,a2)
              (let ([d (arg->var a2)])
                (map (lambda (v)
                  (unless (equal? v d)
                    (add-edge graph d v)))
                  live-vars))]
            [`(negq ,arg)
              (let ([d (arg->var arg)])
                (map (lambda (v)
                  (unless (equal? v d)
                    (add-edge graph d v)))
                  live-vars))]
            [`(callq ,_) "no graph changes needed"]
            [else (error "invalid instruction syntax" instr)]))
          body live-afters)
        `(program
            ,@(append
                (list (list vars graph))
                body)))]
    [else (error "invalid program syntax" p)]))

(define (arg->var arg)
  (match arg
    [`(var ,v) v]
    [else #f]))

; input: (program (var* graph) instr+)
; output: (program stack-size instr+)
(define (allocate-registers p)
  (match p
    [`(program (,var ,graph) ,body ...)
      (let ([color-map (color-graph graph var)]
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
          var)
        (cons
          `program
          (cons
            ; (* 8 (if (< (- max-color 7) 0) 0 (- max-color 7)))
            (* 8 max-color)
            (map (assign-homes-r m) body))))]
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
;         (cons `program (cons (* -1 location) (map (assign-homes-r m) body))))]
;     [else (error "invalid program" p)]))

(define (assign-homes-r m)
  (lambda (e)
    (match e
      [`(int ,num) e]
      [`(var ,v) (hash-ref m v)]
      [`(reg ,r) e]
      [`(callq ,func) e]
      [`(movq ,a1 ,a2)
        `(movq
          ,((assign-homes-r m) a1)
          ,((assign-homes-r m) a2))]
      [`(negq ,arg)
        `(negq ,((assign-homes-r m) arg))]
      [`(addq ,a1 ,a2)
        `(addq
          ,((assign-homes-r m) a1)
          ,((assign-homes-r m) a2))]
      [else (error "not valid grammar for C0" m)])))

(define (patch-instructions e)
  (match e
    [`(program ,size ,body ...)
      (cons `program (cons size
        (append* (map patch-instructions body))))]
    [`(movq ,a1 ,a2)
      (cond
        [(and
          (stack-ref? a1)
          (stack-ref? a2))
          `((movq ,a1 (reg rax))
            (movq (reg rax) ,a2))]
        [(equal? a1 a2) (list)]
        [else (list e)])]
    [`(addq ,a1 ,a2)
      (if (and
            (stack-ref? a1)
            (stack-ref? a2))
          `((movq ,a1 (reg rax))
            (addq (reg rax) ,a2))
          (list e))]
    [else (list e)]
  ))

(define (stack-ref? arg)
  (match arg
    [`(deref rbp ,num) #t]
    [else #f]))

(define (print-x86 e)
  (match e
    [`(program ,size ,body ...)
      (string-append
        "    .globl main\n"
        "main:\n"
        (if (> size 0)
            (string-append
              "    pushq   %rbp\n"
              "    movq    %rsp, %rbp\n"
              "    subq    $" (format "~a" size) ", %rsp\n")
            "")
        "\n    "
        (string-join (map print-x86 body) "\n    ") "\n"
        "\n"
        "    movq    %rax, %rdi\n"
        "    callq   print_int\n"
        "    movq    $0, %rax\n"
        (if (> size 0)
            (string-append
              "    addq    $" (format "~a" size) ", %rsp\n"
              "    popq    %rbp\n")
            "")
        "    retq"
      )]
    [`(movq ,a1 ,a2)
      (format
        "movq    ~a, ~a"
        (print-x86 a1)
        (print-x86 a2))]
    [`(addq ,a1 ,a2)
      (format
        "addq    ~a, ~a"
        (print-x86 a1)
        (print-x86 a2))]
    [`(negq ,arg)
      (format
        "negq    ~a"
        (print-x86 arg))]
    [`(callq ,label)
      (format "callq   ~a" label)]
    [`(int ,num)
      (format "$~a" num)]
    [`(reg ,r)
      (format "%~a" r)]
    [`(deref ,reg ,offset)
      (format "~a(%~a)" offset reg)]
    [else (error "invalid grammar for print-x86" e)]
  ))

(define r1-passes
  `( ("uniquify" ,uniquify ,interp-scheme)
     ("flatten" ,flatten ,interp-C)
     ("select-instructions" ,select-instructions ,interp-x86)
     ("uncover-live" ,uncover-live ,interp-x86)
     ("build-interference" ,build-interference ,interp-x86)
     ("allocate-registers" ,allocate-registers ,interp-x86)
     ; ("assign-homes" ,assign-homes ,interp-x86)
     ("patch-instructions" ,patch-instructions ,interp-x86)
     ("print-x86" ,print-x86 #f)
  ))
