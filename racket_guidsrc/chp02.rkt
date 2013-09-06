#lang racket

; Local bindings with let.
(let ([x (random 4)]
      [y (random 4)])
  (cond
    [(> x y) "X wins"]
    [(> y x) "Y wins"]
    [else "cat's game"]))

; Allows later clauses to use earlier bindings.
(let* ([x (random 4)]
       [y (random 4)]
       [diff (number->string (abs (- x 0)))])
  (cond
    [(> x y) (string-append "X wins by " diff)]
    [(> y x) (string-append "Y wins by " diff)]
    [else "cat's game"]))

; The usage of map.
(map (lambda (s n) (substring s 0 n))
     (list "peanuts" "popcorn" "crackerjack")
     (list 6 3 7))

; foldl generalizes some iteration functions. It uses the per-element function to
; both process an element and combine it with the "current" value, so the per-element function
; takes an extra first argument.
(foldl (lambda (elem v)
         (+ v (* elem elem)))
       0
       '(1 2 3 4))

; Primitive iteration using a handful of list primitives.
(define (my-map-primitive f lst)
  (cond
    [(empty? lst) empty]
    [else (cons (f (first lst))
                (my-map-primitive f (rest lst)))]))

; Reduce constant space factor by accumulating the result list.
(define (my-map-cspace f lst)
  (define (iter lst backward-result)
    (cond
      [(empty? lst) (reverse backward-result)]
      [else (iter (rest lst)
                  (cons (f (first lst))
                        backward-result))]))
  (iter lst empty))

; Syntactic convenience of above code.
(define (my-map f lst)
  (for/list ([i lst])
            (f i)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; With the fact that tail-recursive programs automatically run the same as a loop,
;;; lead Racket programmers to embrace recursive forms rather than avoid them.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Remove consecutive duplicates from a list.
(define (remove-duplicate l)
  (cond
    [(empty? l) empty]
    [(empty? (rest l)) l]
    [else
      (let ([i (first l)])
        (if (equal? i (first (rest l)))
          (remove-duplicate (rest l))
          (cons i (remove-duplicate (rest l)))))]))

(remove-duplicate (list "a" "a" "b" "b" "b" "c" "c"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; In general, this function consumes O(n) space for an input list of length n, but that's fine,
;;; since it produces an O(n) result. If the input list happens to be mostly consecutive duplicates,
;;; then the resulting list can be much smaller than O(n)--and remove-dups will also use much
;;; less than O(n) space! The reason is that when the function discards duplicates, it returns the
;;; result of a remove-dups call directly,
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
