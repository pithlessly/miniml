(import (chicken process-context))
(import (chicken bitwise))
#;
(import (chicken port))

(define (curry2 f) (lambda (a) (lambda (b)             (f a b)   )))
(define (curry3 f) (lambda (a) (lambda (b) (lambda (c) (f a b c)))))

; =================
; MiniML primitives
; =================

(define miniml-&&   (lambda (a) (lambda (b) (and a b))))
(define miniml-||   (lambda (a) (lambda (b) (or a b))))
(define miniml-not  not)
(define miniml-+    (curry2 +))
(define miniml--    (curry2 -))
(define miniml-*    (curry2 *))
(define miniml-/    (curry2 /))

(define miniml->= (curry2 >=))
(define miniml-<= (curry2 <=))
(define miniml->  (curry2 >))
(define miniml-<  (curry2 <))

(define miniml-=
  (lambda (a) (lambda (b)
    (cond
      ((or (integer? a) (char? a) (string? a)) (equal? a b))
      (else (error "the = function claims to be polymorphic, but in reality we only support comparing ints, chars, and strings"))))))
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
(define miniml-char_of_int integer->char)
(define (miniml-print_endline s)
  (display s)
  (display "\n"))
(define (miniml-prerr_endline s)
  (display s (current-error-port))
  (display "\n" (current-error-port)))
(define miniml-invalid_arg error)
(define miniml-exit        exit)
(define (miniml-ref x)   (vector 'ref x))
(define (miniml-deref r) (vector-ref r 1))
(define  miniml-:=       (lambda (r) (lambda (x) (vector-set! r 1 x))))
(define miniml-cons      (curry2 cons))
(define miniml-@         (curry2 append))
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
; Avoid using Scheme builtin map since it doesn't guarantee evaluation order.
; I didn't think this would be a problem, but Chez runs `f` on the elements
; in reverse order.
(define miniml-List.map
  (lambda (f) (lambda (xs)
    (let loop ((acc '()) (xs xs))
      (if (null? xs)
        (reverse acc)
        (let ((y (f (car xs))))
          (loop (cons y acc) (cdr xs))))))))
(define miniml-List.map2
  (lambda (f) (lambda (xs) (lambda (ys)
    (let loop ((acc '()) (xs xs) (ys ys))
      (cond
        ((and (null? xs) (null? ys)) (reverse acc))
        ((and (pair? xs) (pair? ys)) (let ((y ((f (car xs)) (car ys))))
                                       (loop (cons y acc) (cdr xs) (cdr ys))))
        (else (error "Lists differ in length"))))))))
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

(define miniml-Char.<= (curry2 char<=?))
(define miniml-Char.>= (curry2 char>=?))
(define miniml-Char.<  (curry2 char<?))
(define miniml-Char.>  (curry2 char>?))

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
(define (miniml-Option.unwrap opt)
  (if (pair? opt)
    (car opt)
    (error "Option.unwrap: None")))

(define miniml-In_channel.open_text open-input-file)
(define (miniml-In_channel.input_all port)
  (let loop ((chars '()))
    (define char (read-char port))
    (if (eof-object? char)
      (list->string (reverse chars))
      (loop (cons char chars)))))
(define miniml-In_channel.close close-input-port)

(define miniml-Miniml.log_level
  (let ((debug (get-environment-variable "MINIML_DEBUG")))
    (cond
      ((equal? debug "2") 2)
      ((equal? debug "1") 1)
      (else 0))))

(define (miniml-Miniml.debug msg)
  (if (< miniml-Miniml.log_level 1) '()
    (miniml-prerr_endline
      (string-append "\033[33m(debug)\033[m " (msg '())))))
(define (miniml-Miniml.trace msg)
  (if (< miniml-Miniml.log_level 2) '()
    (miniml-prerr_endline
      (string-append "\033[33m(trace)\033[m " (msg '())))))

; =====================================================
; Helpers to throw an error upon a failed pattern match
; =====================================================

(define (miniml-match-failure)
  (error "no pattern in match expression matched"))
(define-syntax miniml-let-guard
  (syntax-rules () ((miniml-let-guard c)
   (define tmp (if c '()
                     (error "irrefutable pattern in let binding did not match"))))))
(define-syntax miniml-fun-guard
  (syntax-rules () ((miniml-fun-guard c)
   (define tmp (if c '()
                     (error "irrefutable fun argument pattern did not match"))))))

; ===================================
; Persistent hash trie implementation
; ===================================

; hashtrie        = cons size tree<32>
; tree<0>         = collision-chain
; tree<n+1>       = nil | entry | cons tree<n> tree<n>
; collision-chain = list(entry)
; entry           = vector hash k v
; convention: the key equality function (k-eql) is always uncurried;
;             the value equality function is curried.

(define hashtrie-empty '(0 . ()))
(define (ht-hash  entry) (vector-ref entry 0))
(define (ht-key   entry) (vector-ref entry 1))
(define (ht-value entry) (vector-ref entry 2))

(define (hashtrie-singleton hash k v)
  (cons 1 (vector hash k v)))

(define (hashtrie-entry-matches k-eql? hash k e)
  (and (=      hash (ht-hash e))
       (k-eql? k    (ht-key  e)) ))

(define (hashtrie-lookup k-eql? hash k m)
  #;
  (miniml-prerr_endline (string-append "*** hashtrie-lookup: "
                                       k
                                       " in "
                                       (with-output-to-string (lambda () (write m)))))
  ; returns nil or the relevant entry
  (let loop ((lvl 32)
             (hp hash)
             (branch (cdr m)))
    (cond
      ((zero? lvl) (let loop ((collision-chain branch))
                     (cond ((null? collision-chain) '())
                           ((hashtrie-entry-matches k-eql? hp k (car collision-chain)) (car collision-chain))
                           (#t (loop (cdr collision-chain))))))
      ((null?   branch) '())
      ((vector? branch) (if (hashtrie-entry-matches k-eql? hash k branch) branch '()))
      ((pair?   branch) (loop (- lvl 1)
                              (arithmetic-shift hp -1)
                              (if (even? hp) (car branch) (cdr branch)))))))

(define (hashtrie-eql? k-eql?) ; key equality function (uncurried)
  (lambda (v-eql?)                    ; value equality function (curried)
    (lambda (m1) (lambda (m2)
      ; compare two collision-chains without order
      (define (collision-chain-eql? c1 c2)
        (if (null? c1) (null? c2)
          (let ((e1 (car c1)))
            (let loop ((prefix '())
                       (suffix c2))
              (cond ((null? suffix) #f)
                    ((k-eql? (ht-key e) (ht-key (car suffix)))
                     (and ((v-eql? (ht-value e)) (ht-value (car suffix)))
                          (collision-chain-eql? (cdr c1) (append prefix (cdr suffix)))))
                    (#t (loop (cons (car suffix) prefix) (cdr suffix))))))))
      (and (= (car m1) (car m2))
           ; recursively compare the trees
           (let loop ((lvl 32)
                      (b1 (cdr m1))
                      (b2 (cdr m2)))
             (cond
               ((zero? lvl)  (collision-chain-eql? b1 b2))
               ((null? b1)   (null? b2))
               ((pair? b1)   (and (pair? b2)
                                  (loop (- lvl 1) (car b1) (car b2))
                                  (loop (- lvl 1) (cdr b1) (cdr b2))))
               ((vector? b1) (and (vector? b2)
                                  ( =      (ht-hash  b1)  (ht-hash  b2))
                                  ( k-eql? (ht-key   b1)  (ht-key   b2))
                                  ((v-eql? (ht-value b1)) (ht-value b2)) )))))))))

(define (hashtrie-merge e0 h0 e1 h1 lvl)
  (if (zero? lvl)
    (list e0 e1)
    (let* ((shift (- lvl 32))
           (bit0 (even? (arithmetic-shift h0 shift)))
           (bit1 (even? (arithmetic-shift h1 shift))))
      (if bit0 (if bit1 (cons (hashtrie-merge e0 h0 e1 h1 (- lvl 1)) '())
                        (cons e0 e1))
               (if bit1 (cons e1 e0)
                        (cons '() (hashtrie-merge e0 h0 e1 h1 (- lvl 1))))))))

(define (hashtrie-insert k-eql? hash k v m)
  (if (not (null? (hashtrie-lookup k-eql? hash k m))) '()
    (let*
      ((new-entry (vector hash k v))
       (new-tree  (let loop ((lvl 32)
                             (hp hash)
                             (branch (cdr m)))
                    (cond
                      ((zero? lvl) (cons new-entry branch))
                      ((null? branch) new-entry)
                      ((vector? branch) (hashtrie-merge branch (ht-hash branch) new-entry hash lvl))
                      ((pair? branch) (let ((new-lvl (- lvl 1))
                                            (new-hp (arithmetic-shift hp -1)))
                                        (if (even? hp)
                                          (cons (loop new-lvl new-hp (car branch)) (cdr branch))
                                          (cons (car branch) (loop new-lvl new-hp (cdr branch))))))))))
      (cons (+ 1 (car m)) new-tree))))

(define hashtrie-map (lambda (f) (lambda (m)
  (define (map-entry e)
    (define hash (ht-hash  e))
    (define k    (ht-key   e))
    (define v    (ht-value e))
    (vector hash k ((f k) v)))
  (cons (car m)
        (let loop ((branch (cdr m)))
          (cond
            ((null?   branch) '())
            ((vector? branch) (map-entry branch))
            ((pair?   branch) (cons (loop (car branch))
                                    (loop (cdr branch))))))))))

(define hashtrie-fold (lambda (f) (lambda (x) (lambda (m)
  (let loop ((branch (cdr m))
             (acc x))
    (cond ((null?   branch) acc)
          ((vector? branch) ((f acc) (vector (ht-key branch) (ht-value branch))))
          ((pair?   branch) (loop (cdr branch) (loop (car branch) acc)))))))))

(define (all-pairs p l1 l2)
  (or (null? l1)
      (null? l2)
      (and (let loop ((l2rest l2)) (and (p (car l1) (car l2rest)) (loop (cdr l2rest))))
           (all-pairs p (cdr l1) l2))))

(define (hashtrie-disjoint-union key-eql? duplicate-key m1 m2)
  (cons
    (+ (car m1) (car m2))
    (let loop ((lvl 32)
               (b1 (cdr m1))
               (b2 (cdr m2)))
      (define (loop-pair b1 b2) (cons (loop (- lvl 1) (car b1) (car b2))
                                      (loop (- lvl 1) (cdr b1) (cdr b2))))
      (define (develop entry) (if (even? (arithmetic-shift (ht-hash entry) (- lvl 32)))
                                (cons entry '())
                                (cons '() entry)) )
      (cond
        ((zero? lvl)             (all-pairs (lambda (e1 e2)
                                              (define k1 (ht-key e1))
                                              (define k2 (ht-key e2))
                                              (or (not (key-eql? k1 k2)) (duplicate-key k1)))
                                            b1 b2))
        ((null? b1)              b2)
        ((null? b2)              b1)
        ((and (pair? b1)
              (pair? b2))        (loop-pair b1 b2))
        ((pair? b1)              (loop-pair b1 (develop b2)))
        ((pair? b2)              (loop-pair (develop b1) b2))
        ((and (= (ht-hash b1)
                 (ht-hash b2))
              (key-eql?
                (ht-key b1)
                (ht-key b2)))   (duplicate-key (ht-key b1)))
        (#t                      (loop-pair (develop b1) (develop b2)))))))

; ====================================================
; StringMap primitives implemented using the hash trie
; ====================================================

(define (string-hash s)
  ; FNV
  (let loop ((i 0)
             (hash #x811c9dc5))
    (if (< i (string-length s))
      (loop (+ i 1)
            (bitwise-xor (char->integer (string-ref s i))
                         (bitwise-and #xffffffff
                                      (* hash #x01000193))))
      hash)))

(define miniml-StringMap.empty hashtrie-empty)
(define (miniml-StringMap.singleton kv) (hashtrie-singleton (string-hash (miniml-fst kv))
                                                            (miniml-fst kv)
                                                            (miniml-snd kv)))
(define miniml-StringMap.lookup (lambda (k) (lambda (m)
  (define entry (hashtrie-lookup string=? (string-hash k) k m))
  #;
  (miniml-prerr_endline (string-append "*** miniml-StringMap.lookup: "
                                       (with-output-to-string (lambda () (write entry)))))
  (if (null? entry) '() (list (ht-value entry))))))
(define miniml-StringMap.eql (hashtrie-eql? string=?))
(define miniml-StringMap.insert (lambda (kv) (lambda (m)
  (define k (miniml-fst kv))
  (define v (miniml-snd kv))
  (define new-map (hashtrie-insert string=? (string-hash k) k v m))
  #;
  (miniml-prerr_endline (string-append "*** miniml-StringMap.insert: k="
                                       k
                                       " v="
                                       (with-output-to-string (lambda () (write v)))
                                       " m="
                                       (with-output-to-string (lambda () (write m)))
                                       " => "
                                       (with-output-to-string (lambda () (write new-map)))))
  (if (null? new-map) '() (list new-map)))))
(define miniml-StringMap.map       hashtrie-map)
(define miniml-StringMap.fold_left hashtrie-fold)
(define miniml-StringMap.disjoint_union (lambda (m1) (lambda (m2)
  (call/cc (lambda (k)
    (vector 'Ok (hashtrie-disjoint-union
                  string=?
                  (lambda (dup-key) (k (vector 'Error (vector 'DupErr dup-key))))
                  m1 m2)))))))
