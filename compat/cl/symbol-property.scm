(define-module (compat cl symbol-property)
  #:use-module (syntax id-table)
  #:export (get put remprop))

#|
  This system, deviates a little from common lisp and is closer to scheme
  1. this system is _much_ slower then CL
  2. the symbols are hashed to their syntax identity this means
     i)  Unbounded symbols will be treated as the same independent of module
     ii) Bounded symbols will be treated to their bounded placeholder
  3. symbol identities will just be symbols and there might be confusion if
     the same symbol is used in different modules.
  4. This implementation is not thread safe.
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

(define wmake-table make-weak-bound-id-table)
(define wref        weak-free-id-table-ref)
(define wset!       weak-free-id-table-set!)

(define symbol-table (wmake-table))
(define-syntax get-var 
  (lambda (stx)    
    (let* ((module (resolve-module (cdr (vector-ref stx 3))))
	   (v      (gensym (ran stx 'sym-props)))
	   (s      (datum->syntax stx v)))
      (let ((r (wref symbol-table stx #f)))
	(with-syntax (((s code)
	(if r 
	    (list r #f)
	    (begin
	      (module-define! module v '(symbols-properties))
	      (wset! symbol-table stx s)
	      (list s 
		    (with-syntax ((stx stx)
				  (s   s))
			  #`(let ((module (resolve-module 
					   '#,(datum->syntax
					       #'1 
					       (cdr (vector-ref #'stx 3))))))
			  
			      (module-define! module 's '(symbols-properties))
			      (wset symbol-table #'stx #'s))))))))

	#'(begin
	    (eval-when (load) code)
	    s))))))
    
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

