(define (curry2 f) (lambda (a) (lambda (b)             (f a b)   )))
(define (curry3 f) (lambda (a) (lambda (b) (lambda (c) (f a b c)))))

(define miniml-&&   (lambda (a) (lambda (b) (and a b))))
(define miniml-||   (lambda (a) (lambda (b) (or a b))))
(define miniml-not  not)
(define miniml-+    (curry2 +))
(define miniml--    (curry2 -))

(define (make-ordered-comparison comp-int comp-char)
  (lambda (a) (lambda (b)
    (cond
      ((integer? a) (comp-int a b))
      ((char? a) (comp-char a b))
      (else (error "the comparison functions claim to be polymorphic, but in reality we only support comparing ints and chars"))))))
(define miniml->= (make-ordered-comparison >= char>=?))
(define miniml-<= (make-ordered-comparison <= char<=?))
(define miniml->  (make-ordered-comparison  >  char>?))
(define miniml-<  (make-ordered-comparison  <  char<?))

(define miniml-=
  (lambda (a) (lambda (b)
    (cond
      ((or (integer? a) (char? a) (string? a)) (equal? a b))
      (else (error "the = function claims to be polymorphic, but in reality we only support comparint ints, chars, and strings"))))))
(define miniml-<>
  (lambda (a) (lambda (b)
    (not ((miniml-= a) b)))))
(define miniml-== (curry2 eq?))
(define miniml-^  (curry2 string-append))
(define miniml-semicolon (lambda (a) (lambda (b) b)))

(define miniml-min     (curry2 min))
(define (miniml-fst t) (vector-ref t 0))
(define (miniml-snd t) (vector-ref t 1))
(define (miniml-int_of_string s)
  (define n (string->number s))
  (cond
    ((not n) (error "int_of_string: could not parse string as a number"))
    ((not (integer? n)) (error "int_of_string: string was a number, but not an integer"))
    (else n)))
(define miniml-string_of_int number->string)
(define miniml-int_of_char char->integer)
(define (miniml-print_endline s)
  (display s)
  (display "\n"))
(define (miniml-prerr_endline s)
  (display s (current-error-port))
  (display "\n" (current-error-port)))
(define miniml-invalid_arg error)
(define miniml-exit        exit)
(define (miniml-ref x) (vector 'ref x))
(define (miniml-! r)   (vector-ref r 1))
(define  miniml-:=     (lambda (r) (lambda (x) (vector-set! r 1 x))))
(define miniml-cons    (curry2 cons))
(define miniml-@       (curry2 append))
(define miniml-List.rev reverse)
(define miniml-List.fold_left
  (lambda (f) (lambda (acc) (lambda (xs)
    (let loop ((acc acc) (xs xs))
      (if (null? xs)
        acc
        (loop ((f acc) (car xs))
              (cdr xs))))))))
(define miniml-List.fold_right
  (lambda (f) (lambda (xs) (lambda (acc)
    (let loop ((acc acc) (xs (reverse xs)))
      (if (null? xs)
        acc
        (loop ((f (car xs)) acc)
              (cdr xs))))))))
(define miniml-List.map  (curry2 map))
(define miniml-List.map2 (lambda (f) (lambda (xs) (lambda (ys)
                           (map (lambda (x y) ((f x) y)) xs ys)))))
(define miniml-List.mapi
  (lambda (f) (lambda (xs)
    (let loop ((acc '()) (i 0) (xs xs))
      (if (null? xs)
        (reverse acc)
        (let ((y ((f i) (car xs))))
          (loop (cons y acc) (+ i 1) (cdr xs))))))))
(define miniml-List.find_opt
  (lambda (p) (lambda (xs)
    (let loop ((xs xs))
      (cond ((null? xs)   '())
            ((p (car xs)) (list (car xs)))
            (else         (loop (cdr xs))))))))
(define miniml-List.iter   (curry2 for-each))
(define miniml-List.length length)
(define miniml-List.concat (lambda (xss) (apply append xss)))

(define miniml-String.length string-length)
(define miniml-String.get (curry2 string-ref))
(define miniml-String.sub (lambda (s) (lambda (start) (lambda (len)
                            (substring s start (+ start len))))))
(define miniml-String.concat
  (lambda (sep) (lambda (s)
    (let loop ((s s) (parts '()))
      (if (null? s)
        (apply string-append (reverse parts))
        (loop (cdr s)
              (cons (car s)
                    (if (null? parts) parts
                        (cons sep parts)))))))))
(define miniml-String.make (curry2 make-string))

(define (miniml-Fun.id x) x)
(define miniml-Fun.flip
  (lambda (f) (lambda (x) (lambda (y) ((f y) x)))))

(define miniml-Option.map (curry2 map))
(define (miniml-Option.get opt)
  (if (pair? opt)
    (car opt)
    (error "Option.get: None")))

(define miniml-In_channel.open_text open-input-file)
(define (miniml-In_channel.input_all port)
  (let loop ((chars '()))
    (define char (read-char port))
    (if (eof-object? char)
      (list->string (reverse chars))
      (loop (cons char chars)))))
(define miniml-In_channel.close close-input-port)

(define (miniml-match-failure)
  (miniml-failure "no pattern in match expression matched"))
(define (miniml-let-guard c)
  (if c '()
        (miniml-failure "irrefutable pattern in let binding did not match")))
(define (miniml-fun-guard c)
  (if c '()
        (miniml-failure "irrefutable fun argument pattern did not match")))
