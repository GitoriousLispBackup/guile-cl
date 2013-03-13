(define-module (compat cl symbol-property)
  #:use-module (syntax id-table)
  #:export (get put remprop))

(define (thin-stx stx)  
  (let* ((sym (syntax->datum stx))
	 (rib (let loop ((ribs (reverse (vector-ref stx 2))))
		(if (pair? ribs)
		    (let* ((rib    (car ribs))
			   (v-vars (if (vector? rib)
				       (vector-ref rib 1)
				       '()))
		           (vars   (if (null? v-vars) 
				       '() 
				       (if (pair? v-vars)
					   v-vars
					   (vector->list v-vars)))))
		      (if (vector? rib)
			  (if (member sym vars)
			      (vector-ref rib 3)
			      (loop (cdr ribs)))
			  '()))
		    '())))
	 (dir  (cdr (vector-ref stx 3))))
    (if (keyword? sym)
	sym
	(if (null? rib)	    
	    (let ((v (catch #t
			    (lambda () (module-ref (resolve-module dir) sym))
			    (lambda x #f))))
	      (if v
		  v
		  (list sym dir)))
	    rib))))

#|
  This system, deviates a little from common lisp and is closer to scheme
  1. this system is almost as dast as CL
  2. the symbols are hashed to their syntax identity in some dynamic way
     this means
     i)   Toplevel bound variables will be cashed to the current symbol 
          variable identity if it exists at compile time.
     ii)  Toplevel variables that cannot be connected to a variable is maped
          to (sym dir)
     ii)  Local Bounded symbols will be treated to their bounded placeholder
     iii) Keywords are treated literally
  3. This implementation is not thread safe.
|#

(define (ran stx nm)
  (define N 1000000000000)
  (let ((s   (modulo (* (hash stx N) (random N))
		     N)))
    (set! *random-state* (seed->random-state s))
    (format #f "~a-~a~a~a~a~a~a" nm 
	    (number->string (random 36) 36)
	    (number->string (random 36) 36)
	    (number->string (random 36) 36)
	    (number->string (random 36) 36)
	    (number->string (random 36) 36)
	    (number->string (random 36) 36))))

;(define wmake-table make-weak-bound-id-table)
(define reftable (make-weak-value-hash-table))
(define wmake-table make-weak-key-hash-table)
(define wref  (lambda* (tab k #:optional (fail #f))
		       (hash-ref tab (thin-stx k) fail)))
(define wset! (lambda (tab k v)
		(let ((kk (thin-stx k)))
		  (hash-set! reftable kk (syntax->datum k))
		  (hash-set! tab kk v))))

(define symbol-table (wmake-table))
(define-syntax get-var 
  (lambda (stx)
    (syntax-case stx ()
      ((_ stx)
       (let* ((module (resolve-module '(compat cl symbol-property)))
	      (v      (gensym (ran #'stx 'sym-props)))
	      (s      (datum->syntax #'stx v)))
      (let ((r (wref symbol-table #'stx #f)))
	(with-syntax (((s code)
	(if r 
	    (list r #f)
	    (begin
	      (module-define! module v '(symbols-properties))
	      (wset! symbol-table #'stx s)
	      (list s 
		    (with-syntax ((stx #'stx)
				  (s   s))
			  #`(let ((module (resolve-module 
					   '(compat cl symbol-property))))
			  
			      (module-define! module 's '(symbols-properties))
			      (wset symbol-table #'stx #'s))))))))

	#'(begin
	    (eval-when (load) code)
	    (@@ (compat cl symbol-property) s)))))))))
    
(define (_get s i d)
  (let ((r (assoc i (cdr s))))
    (if (pair? r)
	(cdr r)
	d)))

(define (_put s i v)
  (let ((q (assoc i (cdr s))))
    (set-cdr! s (if (pair? q)
		   (begin (set-cdr! q v) (cdr s))
		   (cons (cons i v) (cdr s)))))
  
  (if #f #f))

(define (_remprop s i)
  (if (assoc i (cdr s))
      (set-cdr! s (assoc-remove! i (cdr s)))
      #f))

(define-syntax get
  (lambda (x)
    (syntax-case x ()
      ((get symbol indicator)
       #'(get symbol indicator #f))
      ((get symbol indicator default)
       (identifier? #'symbol)
       #'(_get (get-var symbol) indicator default)))))

(define-syntax put
  (lambda (x)
    (syntax-case x ()
      ((get symbol indicator value)
       (identifier? #'symbol)
       #'(_put (get-var symbol) indicator value)))))


(define-syntax remprop
  (lambda (x)
    (syntax-case x ()
      ((get symbol indicator)
       (identifier? #'symbol)
       #'(_remprop (get-var symbol) indicator)))))

