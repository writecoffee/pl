#lang racket

(integer->char 65)
(display #\A)

(parameterize ([current-locale "D"])
              (string-locale-upcase "Strabe"))

(display "\316\273")

; Display of a normal byte string prints the UTF-8 encoding of the string.
(display "\316\273")

; Display the raw bytes with no encoding.
(display #"\316\273")

(bytes->string/utf-8 #"\316\273")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; C locale supports ASCII only, so the following code doesn't work:
;;;
;;;     (parameterize ([current-locale "C"])
;;;                   (bytes->string/locale #"\316\273"))
;;;
;;;     bytes->string/locale: byte string is not a valid encoding for the current locale
;;;     byte string: #"\316\273"
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(let ([cvt (bytes-open-converter "cp1253"
                                 "UTF-8")]
      [dest (make-bytes 2)])
  (bytes-convert cvt #"\353" 0 1 dest)
  (bytes-close-converter cvt)
  (bytes->string/utf-8 dest))

; Symbols are case-sensitive, by using #ci prefix or in other ways,
; the reader can be made to case-fold character sequences to arrive at a symbol.
(eq? 'a 'A)
(eq? 'a #ci'A)

; The write function prints a symbol without a ' prefix. The display form of a symbol is
; the same as the corresponding string.
(write 'Apple)
(display 'Apple)
(write '|6|)
(display '|6|)

; The cons procedure constructs pairs
(cons 1 2)
(cons (cons 1 2) 3)
(pair? (cons 1 2))

(member "Keys"
        '("Florida" "Keys" "U.S.A"))
(assoc 'where
       '((when "3:30") (where "Florida") (who "Mickey")))

(define p (mcons 1 2))
p
(set-mcar! p 0)
p
(write p)

(define (strange)
  (define x x)
  x)

(strange)

(define greeting
  (lambda (given #:d surname)
    (string-append "Hello, " given " " surname)))

(greeting "John" #:d "Doe")

; (define (f)
;   (define (log-it what)
;     (printf "~a\n" what))
;   (log-it "running")
;   (log-it "done"))
; 
; (f)

(define (f n)
  (define (call n)
    (if (zero? n)
      (log-it "done")
      (begin
        (log-it "running")
        (f n)
        (call (- n 1)))))
  (define (log-it what)
    (printf "~a\n" what))
  (call n))

; (f 10)

(letrec ([swing
           (lambda (t)
             (if (eq? (car t) 'tarzan)
               (cons 'vine
                     (cons 'tarzan (cddr t)))
               (cons (car t)
                     (swing (cdr t)))))])
  (swing '(vine tarzan vine vine)))


(letrec ([tarzan-in-tree?
           (lambda (name path)
             (or (equal? name "tarzan")
                 (and (directory-exists? path)
                      (tarzan-in-directory? path))))]
         [tarzan-in-directory?
           (lambda (dir)
             (ormap (lambda (elem)
                      (tarzan-in-tree? (path-element->string elem)
                                       (build-path dir elem)))
                    (directory-list dir)))])
  (tarzan-in-tree? "tarzan" (find-system-path 'temp-dir)))


; named let
(define (duplicate pos lst)
  (let dup ([i 0]
            [lst lst])
    (cond
      [(= i pos) (cons (car lst) lst)]
      [else (cons (car lst) (dup (+ i 1) (cdr lst)))])))

(duplicate 2 (list "apple" "cheese burger!" "banana"))

(define (after-groucho lst)
  (cond
    [(member "Groucho" lst) => cdr]
    [else (error "not there")]))

(member "Groucho" '("Harpo" "Groucho" "Zeppo"))

(after-groucho '("Harpo" "Groucho" "Zeppo"))

; (define (print-triangle height)
;   (if (zero? height)
;     (void)
;     (begin
;       (display (make-string height #\*))
;       (newline)
;       (print-triangle (- height 1)))))
; (print-triangle 4)

(define (log-times thunk)
  (printf "Start: ~s\n" (current-inexact-milliseconds))
  (begin0
    (thunk)
    (printf "End..: ~s\n" (current-inexact-milliseconds))))

(log-times (lambda () (sleep 0.1) 0))

(define (enumerate lst)
  (if (null? lst)
    (printf "null list\n")
    (if (null? (cdr lst))
      (printf "~a.\n" (car lst))
      (begin
        (printf "~a, " (car lst))
        (when (null? (cdr (cdr lst)))
          (printf "and "))
        (enumerate (cdr lst))))))
(enumerate '("Larry" "Curly" "Moe"))
(enumerate '())

(define (print-triangle height)
  (unless (zero? height)
    (display (make-string height #\*))
    (newline)
    (print-triangle (sub1 height))))
(print-triangle 4)

(define greeted null)
(define (greet name)
  (set! greeted (cons name greeted))
  (string-append "Hello, " name))

(greet "Athos")

; (define (make-running-total)
;   (let ([n 0])
;     (lambda ()
;       (set! n (+ n 1))
;       n)))
; (define win (make-running-total))
; (define lose (make-running-total))

(define (make-running-total)
  (let ([n 0])
    (lambda ()
      (set! n (+ n 1))
      n)))
(define win (make-running-total))
(define lose (make-running-total))


(win)
(win)
(lose)
(win)


; (define (sum lst)
;   (let loop ([lst lst] [s 0])
;     (if (null? lst)
;       s
;       (loop (cdr lst) (+ s (car lst))))))
; 
; (sum '(1 2 3))

; (define (sum lst)
;   (apply + lst))

(define (sum lst)
  (for/fold ([s 0])
            ([i (in-list lst)])
            (+ s i)))

(define next-number!
  (let ([n 0])
    (lambda ()
      (set! n (add1 n))
      n)))

(next-number!)
(next-number!)
(next-number!)

(define game
  (let ([w 0]
        [l 0])
    (lambda (win?)
      (if win?
        (set! w (+ w 1))
        (set! l (+ l 1)))
      (begin0
        (values w l)
        (set!-values (w l) (values l w))))))

(game #t)
(game #t)
(game #f)

(define (deep n)
  (cond
    [(zero? n) 0]
    [else
      (quasiquote ((unquote n) (unquote (deep (- n 1)))))]))
(deep 8)

(define (build-exp n)
  (add-lets n (make-sum n)))

(define (add-lets n body)
  (cond
    [(zero? n) body]
    [else
      (quasiquote
        (let ([(unquote (n->var n)) (unquote n)])
          (unquote (add-lets (- n 1) body))))]))

(define (make-sum n)
  (cond
    [(= n 1) (n->var 1)]
    [else
      (quasiquote (+ (unquote (n->var n))
                     (unquote (make-sum (- n 1)))))]))

(define (n->var n) (string->symbol (format "x~a" n)))
(build-exp 3)

(quasiquote (1 2 (unquote (+ 3 5))))

