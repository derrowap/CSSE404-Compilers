#! /usr/bin/env racket
#lang racket
(require "utilities.rkt")
(require "interp.rkt")
(require "compiler.rkt")

(debug-level 0)

(interp-tests
    "R4-compiler"           ; name of compiler
    #f               ; type checker or #f to ignore
    r4-passes               ; passes containing methods to test
    interp-scheme           ; interpreter to compare results with
    "r4"                    ; test suite
    (range 1 39)            ; list of numbers for test suite
)

(display "interpreter tests passed!") (newline)

; (compiler-tests
;     "R3-compiler"           ; name of compiler
;     typecheck               ; type checker or #f to ignore
;     r3-passes               ; passes containing methods to test
;     "r3"                    ; test suite name
;     (range 1 36)            ; list of number for test suite
; )

;  (display "compiler tests passed!") (newline)