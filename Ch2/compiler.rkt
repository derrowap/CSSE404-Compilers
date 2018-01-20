#lang racket
(require racket/match)
(require "utilities.rkt")
(require "interp.rkt")

(provide
  uniquify flatten select-instructions assign-homes patch-instructions
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

(define (assign-homes p)
  (match p
    [`(program ,vars ,body ...)
      (let ([m (make-hash)] [location 0])
        (map
          (lambda (v)
            (set! location (- location 8))
            (hash-set! m v `(deref rbp ,location)))
          vars)
        (cons `program (cons (* -1 location) (map (assign-homes-r m) body))))]
    [else (error "invalid program" p)]))

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
      (if (and
            (stack-ref? a1)
            (stack-ref? a2))
          `((movq ,a1 (reg rax))
            (movq (reg rax) ,a2))
          (list e))]
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
     ("assign-homes" ,assign-homes ,interp-x86)
     ("patch-instructions" ,patch-instructions ,interp-x86)
     ("print-x86" ,print-x86 #f)
  ))

