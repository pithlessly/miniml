(import (chicken process-context)) ; for (get-environment-variable), (program-name), (command-line-arguments)
(import (chicken bitwise))         ; for (arithmetic-shift)
#;
(import (chicken port))
(define (miniml-Miniml.argv ())
  (cons
    (program-name)
    (command-line-arguments)))
