#lang racket

#| An S-expression comment teels Racket to ignore the next parenthesized expression |#

; In fact, lists in Racket are just an illusion all of them are actually composed of cons cells. 
; The following two snippets of code are the same.
(cons 1 (cons 2 (cons 3 empty)))
(list 1 2 3)

(define cell (cons 'a 'b))

(cons 'pig (cons 'duck (cons 'chicken empty)))

; Nested list consists solely of cons cells.
(cons (cons 'peas (cons 'carrots (cons 'tomatoes '())))
      (cons (cons 'pork (cons 'beef (cons 'chicken '()))) '()))

; Functions for accessing the first through tenth elements are built in.
(second '((peas carrots tomatoes) (pork beef chicken) duck))
(third '((peas carrots tomatoes) (pork beef chicken) duck))
(first (second '((peas carrots tomatoes)
                 (pork beef chicken)
                 duck)))

