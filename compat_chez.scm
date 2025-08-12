(define get-environment-variable getenv)
(define arithmetic-shift         bitwise-arithmetic-shift)
(load "prelude.scm")
(define miniml-program-args (command-line)) ; also works in Guile
(define (miniml-Miniml.argv _)
  (cdr miniml-program-args))
(load (cadr miniml-program-args))
