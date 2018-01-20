#! /usr/bin/env racket
#lang racket
(require "utilities.rkt")
(require "interp.rkt")
(require "compiler.rkt")

(debug-level 0)

(interp-tests
    "R1-compiler"           ; name of compiler
    #f                      ; type checker or #f to ignore
    r1-passes               ; passes containing methods to test
    interp-scheme           ; interpreter to compare results with
    "r1"                    ; test suite
    (range 1 49)            ; list of numbers for test suite
)

(display "interpreter tests passed!") (newline)

(compiler-tests
    "R1-compiler"           ; name of compiler
    #f                      ; type checker of #f to ignore
    r1-passes               ; same as r1-passes but with the print-x86 step
    "r1"                    ; test suite name
    (range 1 49)            ; list of number for test suite
)

(display "compiler tests passed!") (newline)
