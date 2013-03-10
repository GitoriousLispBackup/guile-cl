(define-module (compat cl block)
  #:use-module ((stis coroutine)
		#:select ((with-coroutines . with)
			  (yield           . return)
			  (yield-from      . return-from)))
  #:export (block)
  #:re-export (return return-from))

(define-syntax block
  (syntax-rules ()
    ((_ name)
     (if #f #f))
    ((_ name form ...)
     (with-coroutines ((name (lambda () form ...)))
       (name)))))
       