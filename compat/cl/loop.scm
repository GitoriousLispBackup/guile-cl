(define-module (compat cl loop)
  #:use-module (syntax parse)
  #:use-module (ice-9 match)
  #:export     (loop return return-from))

(define *initially* (make-fluid '()))
(define *finally*   (make-fluid '()))

(define (D x) (syntax->datum  x))

(define (stx-gen stx nm) (datum->syntax stx (gensym nm)))

(define (1-apply l rest)
  (match l
   (()      rest)
   ((x)     (x rest))
   ((x . l) (x (1-apply l rest)))))

(define (2-apply l f rest)
  (match l
   (()      rest)
   ((x)     (x f rest))
   ((x . l) (x f (2-apply l f rest)))))

(define (append-all l)
  (let loop ((ret '()) (l l))
    (match l
      ((x . l)
       (loop (append x ret) l))
      (() ret))))

(define (append-all! l)
  (let loop ((ret '()) (l l))
    (match l
      ((x . l)
       (loop (append! x ret) l))
      (() ret))))

(define-syntax-rule (next-guard fail x)
  (catch #t
    (lambda () x)
    (lambda y (fail))))

(define tag (make-prompt-tag))
(define-syntax-parameter S (lambda x #'tag))
(define-syntax-rule (return . l)
  (abort-to-prompt S . l))
(define-syntax-rule (return-from S . l)
  (abort-to-prompt S . l))

(begin
  (define-syntax-class compound-form
    (pattern (_ . _)))

  (define-splicing-syntax-class named-clause
    (pattern (~seq (~optional (~seq (~datum named) ~! name)) ...)
      #:attr code 
      (lambda (cc)
	(if name
	    (with-syntax ((name name))
	       #`(let ((name (make-prompt-tag)))
		   (syntax-parameterize ((S (lambda z #'name)))
		     (call-with-prompt S
			(lambda () #,cc)
			(lambda (k . l) 
			  (when (null? l) (set! l (list #f)))
			  (apply values l))))))

	    #`(call-with-prompt S
		 (lambda () #,cc)
		 (lambda (k . l) 
		   (when (null? l) (set! l (list #f)))
		   (apply values l)))))))

  (define-splicing-syntax-class main-clause
    (pattern (~or x:unconditional
		  x:accumulation
		  x:conditional
		  x:termination-test
		  x:initial-final)
       #:attr init x.init
       #:attr body x.body
       #:attr inc  x.inc
       #:attr end  x.end))


  (define-splicing-syntax-class unconditional
    #:attributes ((x 1) f2 type init body inc end)
    (pattern (~or (~seq (~and type (~or (~datum do) (~datum doing))) ~!
			x:compound-form ...+)
		  (~seq (~and type (~datum return))      
			~! f2))
	     #:with (xx ...) (if x x '())
	     #:with ff2 f2
	     #:attr init (lambda (x) x)
	     #:attr body (lambda (fail cc)
			   (case (D #'type)
			     ((do doing)
			      #`(begin xx ... #,cc))
			     ((return)
			      #`(return-from S ff2))))
	     #:attr inc  (lambda (f cc) cc)
	     #:attr end  (lambda (x) x)))

  (define-splicing-syntax-class accumulation
    (pattern (~or xa:list-accumulation
		  xa:numeric-accumulation)
	     #:attr init xa.init
	     #:attr body xa.body
	     #:attr inc  xa.inc
	     #:attr end  xa.end))

  
  (define-splicing-syntax-class list-accumulation
    (pattern (~seq (~and name 
			 (~or (~datum collect)
			      (~datum collecting)
			      (~datum append)
			      (~datum appending)
			      (~datum nconc)
			      (~datum nconcing))) ~!
		  (~and q (~or (~datum it) x))
		  (~optional (~seq (~datum into) ~! v)) ...)
	     
	     #:with acc  (datum->syntax #'x (gensym "acc"))
	     #:with var  (if v v #'acc)	     		
	     #:attr init (lambda (cc) 
			   #`(let ((var '())) #,cc))
	     
	     #:attr body (lambda (fail cc)
			   #`(begin (set! var (cons q var))
				      #,cc))

	     #:attr inc (lambda (f cc) cc)

	     #:attr end  (lambda (cc)
			   (let ((final (case (syntax->datum #'name)
					  ((collect collecting)
					   #'(reverse var))
					  ((append appending)
					   #'(append-all var))
					  ((nconc nconcing)
					   #'(append-all! var)))))
			     (if (not (eq? cc #t))
				 #`(begin (set! var #,final) 
					  #,cc)
				 final)))))
  

  (define-splicing-syntax-class numeric-accumulation
    (pattern (~seq (~and type (~or (~datum count)
				   (~datum counting)
				   (~datum sum)
				   (~datum summing)
				   (~datum maximize)
				   (~datum maximizing)
				   (~datum minimize)
				   (~datum minimizing))) ~!
		   x
		   (~optional (~seq (~datum into) ~! v:id)) ...)
	   #:with X0 (stx-gen #'1 "x0")
	   #:with X  (if v v #'X0)

	   #:attr init 
	   (lambda (cc) 
	     #`(let  ((X #,(case (D #'type)
			     ((maximize maximizing)
			      #'-inf.0)
			     ((minimize minimizing)
			      #'+inf.0)
			     (else 0))))
		 #,cc))

	   #:attr body 
	   (lambda (final cc)
	     (case (D #'type)
	       ((count counting)
		#`(begin (when x (set! X (+ X 1))) #,cc))
	       ((sum summing)
		#`(begin (set! X (+ X x)) #,cc))
	       ((maximize maximizing)
		#`(begin (when (> x X) (set! X x)) #,cc))
	       ((minimize minimizing)
		#`(begin (when (< x X) (set! X x)) #,cc))))

	   #:attr inc (lambda (f cc) cc)
	   #:attr end 
	   (lambda (cc)
	     (if (eq? cc #t) #'X cc))))
		 
  

  (define-splicing-syntax-class conditional
    (pattern (~seq (~and type 
			 (~or (~datum if) (~datum when) (~datum unless))) ~!
		   f xsel:selectable-clause 
		   (~seq (~datum and) ~! xs:selectable-clause) ...
		   (~optional
		    (~seq (~datum else) ~!
			  e:selectable-clause
			  (~seq (~datum and) ~! es:selectable-clause) ...)) ...
		   (~optional (~datum end)) ...)
	     #:with it (datum->syntax #'type 'it)
	     #:attr init 
	     (lambda (cc)
	       (1-apply (append 
			 (cons xsel.init xs.init)
			 (if e.init (cons e.init es.init) '()))
			cc))

	     #:attr body (lambda (fail cc)
			   #`(let ((it f))
			       #,(if e.body
				     #`(if it
					   #,(2-apply 
					      (cons xsel.body xs.body) fail cc)
					   #,(2-apply 
					      (cons e.body    es.body) fail cc))
				     #`(if it 
					   #,(2-apply (cons xsel.body xs.body) 
						      fail
						      cc)
					   #,cc))))
			       
				 
	     #:attr inc  (lambda (f x) x)
	     #:attr end  
	     (lambda (cc)
	       (1-apply (append (cons xsel.end xs.end) 
				(if e.end (cons e.end es.end) '()))
			cc))))


  (define-splicing-syntax-class selectable-clause
    (pattern (~or x:unconditional
		  x:accumulation
		  x:conditional)
      #:attr init x.init
      #:attr body x.body
      #:attr inc  x.inc
      #:attr end  x.end))
	     

  (define-splicing-syntax-class termination-test
    (pattern (~seq (~and type (~or (~datum while) 
				   (~datum until) 
				   (~datum repeat) 
				   (~datum always) 
				   (~datum never)
				   (~datum thereis)))
		   ~! f1)
	 #:with i (stx-gen #'f1 "i")
	 #:with n (stx-gen #'f1 "n")
	 #:with q (stx-gen #'f1 "q")

	 #:attr init (lambda (cc)
		       (case (D #'type)
			 ((repeat)
			  #`(let ((i 0) (n f1)) #,cc))
			 (else cc)))

	 #:attr body (lambda (fail cc)
		       (case (syntax->datum #'type)
			 ((while)
			  #`(if f1 #,cc (#,fail)))
			 ((until)
			  #`(if f1 (#,fail) #,cc))
			 ((repeat)
			  #`(if (< i n) 
				(begin (set! i (+ i 1)) #,cc) 
				(#,fail)))
			 ((always)
			  #`(if f1 #,cc (return-from S #f)))
			 ((never)
			  #`(if f1 (return-from S #f) #,cc))
			 ((there-is)
			  #`(let ((q f1)) (if q (return-from S q) #,cc)))))

	 #:attr inc  (lambda (fail cc) cc)
	 #:attr end  (lambda (x) x)))


  (define-splicing-syntax-class variable-clause
    (pattern (~or x:with-clause 
		  x:initial-final 
		  x:for-as-clause
		  x:termination-test)
       #:attr init x.init
       #:attr body x.body
       #:attr inc  x.inc
       #:attr end  x.end))


  (define-splicing-syntax-class var
    (pattern (~seq v:id)
	     #:with i #f)
    (pattern (~seq v:id x)
	     #:with i #'x))

  (define-splicing-syntax-class with-clause
    (pattern (~seq (~datum with) ~! v:var (~seq (~datum and) vs:var) ...)
	     #:with (vars ...) (cons #'v.v #'(vs.v ...)) 
	     #:with (is   ...) (cons #'v.i #'(vs.i ...))

	 #:attr init 
	 (lambda (cc)
	   #`(let ((vars is) ...) #,cc))
	 #:attr body (lambda (f x) x)
	 #:attr inc  (lambda (f x) x)
	 #:attr end  (lambda (x) x)))


  (define-splicing-syntax-class initial-final
    (pattern (~or
	      (~seq (~and type (~datum initially)) ~! x:compound-form ...+)
	      (~seq (~and type (~datum finally))   ~! x:compound-form ...+))
	     #:attr init 
	     (begin
	       (case (D #'type)
		 ((initially)
		  (fluid-set! *initially* 
			      (cons
			       (lambda (cc) #`(begin x ... #,cc))
			       *initially*)))
		 ((finally)
		  (fluid-set! *finally* 
			      (cons
			       (lambda (cc) #`(begin x ... #,cc))
			       *finally*))))
	       (lambda (x) x))

	     #:attr body (lambda (f x) x)
	     #:attr inc  (lambda (f x) x)
	     #:attr end  (lambda (x) x)))



  (define-splicing-syntax-class for-as-clause
    (pattern (~seq (~or (~datum for) (~datum as)) ~!
		   x-for:for-as-subclause
		   (~seq (~datum and) ~! xs:for-as-subclause) ...)
	 #:attr init (lambda (x) 
		       (1-apply (cons x-for.init xs.init) x))
	 #:attr body (lambda (f x) 
		       (2-apply (cons x-for.body xs.body) f x))
	 #:attr end  (lambda (x) 
		       (1-apply (cons x-for.end  xs.end ) x))
	 #:attr inc  (lambda (f x) 
		       (2-apply (cons x-for.inc  xs.inc ) f x))))
  
  (define-splicing-syntax-class for-as-subclause
    (pattern (~or x:for-as-arithmetic
		  x:for-as-in/on-list
		  x:for-as-equals-then
		  x:for-as-across
		  x:for-as-hash
		  x:for-as-package)
	 
	 #:attr init x.init
	 #:attr body x.body
	 #:attr inc  x.inc
	 #:attr end  x.end))

  
  (define-splicing-syntax-class for-as-arithmetic
    (pattern (~seq v:id (~or x:arithmetic-up
			     x:arithmetic-downto
			     x:arithmetic-downfrom))
	     #:attr init (x.init #'v)
	     #:attr body (x.body #'v)
	     #:attr inc  (x.inc  #'v)
	     #:attr end  (x.end  #'v)))

  
  (define-splicing-syntax-class arithmetic-up
    (pattern (~seq (~or (~optional (~seq (~or (~datum from) 
					      (~datum upfrom)) 
					 f1-up))
			(~optional (~seq (~and type (~or (~datum to)
							 (~datum upto)
							 (~datum below)))
					 f2-up))
			(~optional (~seq (~datum by) f3-up))
			(~seq (~fail #:when #t 
				     "arithmetic up failed"))) ...)
	#:attr init
	(lambda (v)
	  (lambda (cc)
	    (if f1-up
		#`(let ((#,v #,f1-up)) #,cc)
		#`(let ((#,v 0))       #,cc))))

	#:with less (if (and type (eq? (D type) 'below))
			#'<
			#'<=)
		       
	#:attr body
	(lambda (v)
	  (lambda (fail cc)
	    (if f2-up
		#`(if (less #,v #,f2-up) #,cc (#,fail))
		cc)))

	#:attr inc
	(lambda (v)
	  (lambda (fail cc)
	    (if f3-up
		#`(catch #t
			 (lambda () (set! #,v (#,f3-up #,v)) #,cc)
			 (lambda z (#,fail)))
		#`(begin (set! #,v (+ #,v 1)) #,cc))))

	#:attr end (lambda (v) (lambda (cc) cc))))

  (define-splicing-syntax-class arithmetic-downto
    (pattern (~seq (~or (~once    (~seq (~datum from)  f1))
			(~once    (~seq (~and type (~or (~datum downto)
							(~datum above)))
					 ~! f2))
			(~optional (~seq (~datum by) f3))) ...)
	#:with init
	(lambda (v)
	  (lambda (cc)
	    #`(let ((#,v f1)) #,cc)))

	#:with grt (if (eq? (D #'type) 'above)
			#'>
			#'>=)
		       
	#:with body
	(lambda (v)
	  (lambda (fail cc)
	    #`(if (grt #,v f2) #,cc (#,fail))))

	#:with inc
	(lambda (v)
	  (lambda (fail cc)
	    (if f3
		#`(catch #t
			 (lambda () (set! #,v (#,f3 #,v)) #,cc)
			 (lambda z (#,fail)))
		#`(begin (set! #,v (- #,v 1)) #,cc))))

	#:attr end (lambda (v) (lambda (cc) cc))))


  (define-splicing-syntax-class arithmetic-downfrom
    (pattern (~seq (~or (~once (~seq (~datum downfrom) ~! f1))
			(~optional (~seq (~and type (~or (~datum to)
							 (~datum downto)
							 (~datum above)))
					 f2))
			(~optional (~seq (~datum by) f3))) ...)
	#:with init
	(lambda (v)
	  (lambda (cc)
	    #`(let ((#,v f1)) #,cc)))

	#:with grt (if (and type (eq? (D #'type) 'above))
			#'>
			#'>=)
		       
	#:with body
	(lambda (v)
	  (lambda (fail cc)
	    (if type
		#`(if (grt #,v #,f2) #,cc (#,fail))
		cc)))
	  

	#:with inc
	(lambda (v)
	  (lambda (fail cc)
	    (if f3
		#`(catch #t
			 (lambda () (set! #,v (#,f3 #,v)) #,cc)
			 (lambda z (#,fail)))
		#`(begin (set! #,v (- #,v 1)) #,cc))))

	#:attr end (lambda (v) (lambda (cc) cc))))


  (define-splicing-syntax-class for-as-in/on-list
    (pattern (~seq v (~and kind (~or (~datum in) (~datum on))) ~! f1 
		   (~optional (~seq (~datum by) ~! f2)) ...)
	     #:with li     (datum->syntax #'v (gensym "list"))
	     #:with loop   (datum->syntax #'v (gensym "loop"))
	     #:with car-li (case (syntax->datum #'kind)
			     ((in) #'(car li))
			     ((on) #'li))
	     #:attr update 
	     (lambda (fail)
	       (if f2
		   #`(catch #t
			    (lambda () (set! li (#,f2 li)) (loop))
			    (lambda x (#,fail)))
		   #`(begin (set! li (cdr li)) (loop))))

	     #:attr init 
	     (lambda (cc) 
	       #`(let ((li f1)) #,cc))

	     #:attr body 
	     (lambda (fail cc) 
	       #`(let loop ()
		   (if (pair? li)
		       (match car-li
			      (v #,cc)
			      (_ #,(update fail)))
		       (#,fail))))

	     #:attr inc  
	     (lambda (fail cc)	       
	       (if f2
		   #`(catch #t
			    (lambda ()
			      (set! li (#,f2 li)) #,cc)
			    (lambda x (#,fail)))
		   #`(begin (set! li (cdr li)) #,cc)))

	     #:attr end  (lambda (x) x)))
  
  (define-splicing-syntax-class for-as-equals-then
    (pattern (~seq v:id (~datum =) ~! f1 
		   (~optional (~seq (~datum then) f2)) ...)
	     #:with s (stx-gen #'v "iter")
	     #:attr init 
	     (lambda (cc)
	       #`(let ((s f1)) #,cc))
	     
	     #:attr body
	     (lambda (fail cc)
	       #`(let ((v s)) #,cc))

	     #:attr inc
	     (lambda (fail cc)
	       (if f2
		   #`(begin (set! s #,f2) #,cc)
		   cc))

	     #:attr end  
	     (lambda (x) x)))


  (define-splicing-syntax-class for-as-across
    (pattern (~seq v (~datum across) ~! f1)
	     #:with ar   (stx-gen #'v "array")
	     #:with ar-i (stx-gen #'v "i")
	     #:with ar-n (stx-gen #'v "n")
	     #:attr init 
	     (lambda (cc)
	       #`(let* ((ar   f1) 
		        (ar-i 0) 
		        (ar-n (generalized-vector-length ar))) 
		   #,cc))

	     #:attr body
	     (lambda (fail cc) 
	       #`(let loop ()
		   (if (< ar-i ar-n)
		       (match (generalized-vector-ref ar ar-i)
			      (v #,cc)
			      (_ (set! ar-i (+ ar-i 1)) (loop)))
		       (#,fail))))

	     #:attr inc  
	     (lambda (fail cc)
	       #`(begin (set! ar-i (+ ar-i 1)) #,cc))

	     #:attr end  (lambda (x) x)))
  

  (define-splicing-syntax-class for-as-hash
    (pattern (~seq v (~datum being)
		   (~or (~datum each) (~datum the))
		   (~or (~seq (~and type
				    (~or (~datum hash-key) (~datum hash-keys)))
			      (~or (~datum in) (~datum of))
			      ht
			      (~optional (~seq (~datum using) 
					       ((~datum hash-value) ov))) ...)

			(~seq (~and type
				    (~or (~datum hash-value) 
					 (~datum hash-values)))
			      (~or (~datum in) (~datum of))
			      ht
			      (~optional (~seq (~datum using) 
					       ((~datum hash-key) ov))) ...)))

	     #:with li   (stx-gen #'1 "list")
	     #:with loop (stx-gen #'1 "loop")
	     #:with p-key 
	     (case (D #'type)
	       ((hash-key hash-keys)
		#'v)
	       ((hash-value hash-values)
		(if ov ov #'_)))

	     #:with p-value 
	     (case (D #'type)
	       ((hash-key hash-keys)
		(if ov ov #'_))
	       ((hash-value hash-values)
		#'v))
		
	     #:attr init 
	     (lambda (cc)
	       #`(let ((li (hash-map->list cons ht))) #,cc))

	     #:attr body 
	     (lambda (fail cc)
	       #`(let loop ()
		   (if (pair? li)
		       (match (car li)
			  ((p-key . p-value) 
			   #,cc)
			  (_ 
			   (set! li (cdr li))
			   (loop)))
		       (#,fail))))
			   
	     #:attr inc  
	     (lambda (fail cc)
	       #`(begin (set! li (cdr li)) #,cc))

	     #:attr end  
	     (lambda (x) x)))


  (define-splicing-syntax-class for-as-package
    (pattern (~seq v:id (~datum being)
		   (~or (~datum symbol) (~datum symbols)
			(~datum present-symbol)
			(~datum present-symbols)
			(~datum external-symbol)
			(~datum external-symbols)) ~!
		   (~optional (~seq (~or (~datum in) (~datum of))
				    p)) ...)
	     #:attr init (lambda (x) x)
	     #:attr body (lambda (f x) x)
	     #:attr inc  (lambda (f x) x)
	     #:attr end  (lambda (x) x))))
		
(define-syntax loop
  (lambda (x)
    (syntax-parse x
      ((_ (~do (fluid-set! *finally* '()) (fluid-set! *initially* '()))
	       nm:named-clause v:variable-clause ... m:main-clause ...)
	(with-syntax
	 ((loop  (datum->syntax x (gensym "loop")))
	  (final (datum->syntax x (gensym "final")))
	  (it    (datum->syntax x (gensym "it"))))
	 #`(let ()
	     #,(nm.code
		(1-apply (append v.init m.init (reverse 
						(fluid-ref *initially*)))
		  #`(letrec 
			((final 
			  (lambda () 
			    #,(1-apply (append (reverse
						(fluid-ref *finally*)) m.end)
				       #t)))
			 (loop  
			  (lambda () 
			    #,(2-apply (append v.body m.body)
				       #'final
				       (2-apply v.inc #'final #'(loop))))))
		      (loop))))))))))
