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
