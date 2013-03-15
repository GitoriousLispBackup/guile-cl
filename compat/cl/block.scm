(define-module (compat cl block)
  #:use-module (stis coroutine)
  #:export (block return return-from))

(define-syntax-rule  (return . l)      (leave . l))
(define-syntax-rule  (return-from . l) (leave-from . l))

(define-syntax block
  (syntax-rules ()
    ((_ name)
     (if #f #f))
    ((_ name form ...)
     (with-coroutines ((name (lambda () form ...)))
       (name)))))
       