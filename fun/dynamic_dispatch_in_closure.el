;; Manually dynamic dispatch

(defstruct obj fields methods)

(defun get (obj field-name)
  (let ((field-cell (assoc field-name (obj-fields obj))))
    (if field-cell
        (cdr field-cell)
      (error (format "Field %s not found in STRUCT obj!" field-name)))))

(defun set (obj field-name field-new-value)
  (let ((field-cell (assoc field-name (obj-fields obj))))
    (if field-cell
        (setcdr field-cell field-new-value)
      (error (format "Field %s not found in STRUCT obj!" field-name)))))

(defun send-msg (obj msg &rest args)
  (let ((method-cell (assoc msg (obj-methods obj))))
    (if method-cell
        (funcall (cdr method-cell) obj args)
      (error (format "Method %s cannot be found in STRUCT obj!" msg)))))

(defun make-point (_x _y)
  (make-obj :fields (list (cons 'x  _x) (cons 'y  _y))
            :methods (list (cons 'get-x  (lambda (self _)
                                           (get self 'x)))
                           (cons 'get-y  (lambda (self _)
                                           (get self 'y)))
                           (cons 'set-x  (lambda (self args)
                                           (let ((new-value (car args)))
                                             (set self 'x new-value))))
                           (cons 'set-y  (lambda (self args)
                                           (let ((new-value (car args)))
                                             (set self 'y new-value)))))))

(defun make-color-point (_x _y _c)
  (let ((pt (make-point _x _y)))
    (make-obj :fields (append (list (cons 'c  _c)) (obj-fields pt))
              :methods (append (list (cons 'get-color  (lambda (self _)
                                                     (get self 'c)))
                                     (cons 'set-color  (lambda (self args)
                                                         (let ((new-color (car args)))
                                                           (set self 'c new-color)))))
                               (obj-methods pt)))))

(defun make-polar-point (_r _th)
  (let ((pt (make-point (* _r (cos _th))
                        (* _r (sin _th)))))
    (make-obj :fields (append (list (cons 'radius  _r) (cons 'theta  _th))
                              (obj-fields pt))

              :methods (append (list (cons 'set-radius (lambda (self args)
                                                         (let ((new-radius (car args)))
                                                           (set self 'radius new-radius))))
                                     (cons 'set-theta (lambda (self args)
                                                        (let ((new-theta (car args)))
                                                          (set self 'theta new-theta))))

                                     ;; override
                                     (cons 'set-x (lambda (self args)
                                                    (let* ((new-x (car args))
                                                           (current-y (get self 'y))
                                                           (new-theta (atan current-y new-x))
                                                           (new-radius (sqrt (+ (* new-x new-x)
                                                                                (* current-y current-y)))))
                                                      (set self 'x new-x)
                                                      (set self 'radius new-radius)
                                                      (set self 'theta new-theta))))

                                     ;; override
                                     (cons 'set-y (lambda (self args)
                                                    (let* ((new-y (car args))
                                                           (current-x (get self 'x))
                                                           (new-theta (atan new-y current-x))
                                                           (new-radius (sqrt (+ (* new-y new-y)
                                                                                (* current-x current-x)))))
                                                      (set self 'y new-y)
                                                      (set self 'radius new-radius)
                                                      (set self 'theta new-theta)))))
                               (obj-methods pt)))))
