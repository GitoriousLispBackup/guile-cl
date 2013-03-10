(define-module (compat cl tagbody)
  #:use-module (syntax parse)  
  #:use-module ((stis coroutine)
		#:select ((tagbody . tagbody:co)
			  (goto    . go)))
  #:export    (tagbody)
  #:re-export (go))

(define (stx-cdr x)
  (syntax-case x () ((x . l) #'l)))

(define (pp x) (pk (syntax->datum x)) x)
(define-syntax tagbody
  (lambda (x)
    (with-syntax (((forms ...)
		   (let loop ((x (stx-cdr x)) 
			      (tag 
			       (datum->syntax #'1 
					      (gensym "start"))))
		     (syntax-parse x
		        (((~and x (~not :id)) ... n:id . l)
			 #`((#,tag x ...) #,@(loop #'l #'n)))
			((x ...)
			 #`((#,tag x ...)))))))
	(pp #'(begin (tagbody:co forms ...) (if #f #f))))))