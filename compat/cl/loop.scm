(define-module (compat cl loop)
  #:use-module (compat cl block)
  #:use-module (syntax parse)
  #:use-module (syntax parse debug)
  #:use-module (ice-9 match)
  #:export     (debug-loop loop it)
  #:re-export (return return-from))

(define-syntax-parameter *list-end-test* 
  (syntax-rules () ((_ x) (pair? x))))

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

(define (pattern->vars stx)
  (define oldvars '())
  (define newvars '())
  (define (get-pat stx)
    (let loop ((stx stx))
      (syntax-case stx (quote and or not ? = _ $ vector)
	((x . l)
	 (let ((n (syntax->datum #'x)))
	   (member n '(... ___ ..1 ***)))
	 #`(x ,@(loop #'l)))
	((and . l)
	 #`(and #,@(loop #'l)))
	((or  . l)
	 #`(or #,@(loop #'l)))
	(($ n l ...)
	 #`($ n #,@(map loop #'(l ...))))
	((vector l ...)
	 #`(vector #,@(map loop #'(l ...))))
	((not  l)
	 #`(not #,(loop #'l)))
	((quote l)
	 #`(quote #,(loop #'l)))
	((? f . l)
	 #`(? f ,@(loop #'l)))
	((= f l)
	 #`(= f ,@(loop #'l)))
	((x . l)
	 #`(or () (#,(loop #'x) . #,(loop #'l)))) ;; loop's sloppy matcher
	(_ stx)
	(x
	 (identifier? #'x)
	 (let ((s (datum->syntax #'1 (gensym "temp"))))
	   (set! oldvars (cons #'x oldvars))
	   (set! newvars (cons s   newvars))
	   s))
	(x #'x))))

  (define newpat (map get-pat stx))

  (list newpat newvars oldvars))

(define-syntax-rule (next-guard fail x)
  (catch #t
    (lambda () x)
    (lambda y (fail))))

;; it utilitiy
(define-syntax-parameter it 
  (lambda x (error "compat cl loop it cannot be used outside loop")))
(define-syntax with-it
  (lambda (x)
    (syntax-case x ()
    ((_ code ...)
     (with-syntax ((s (datum->syntax #'1 
				     (gensym "it"))))
          #'(syntax-parameterize ((it (lambda (x) #'s))) code ...))))))

    

;; termination utilities
(define-syntax-parameter T
  (lambda (x) (error "terminate cannot be used outside of iterate macro")))
(define-syntax-rule (terminate) (abort-to-prompt T))
(define-syntax-rule (finish)    (abort-to-prompt T))
(define-syntax with-finally 
  (lambda (x)
    (syntax-case x ()
    ((_ code codef)
     (with-syntax ((s (datum->syntax #'1 
				     (gensym "finally-prompt"))))
          #'(syntax-parameterize ((T (lambda (x) #''s)))
	      (call-with-prompt T
		 (lambda () code)
		 (lambda x  codef))))))))

;; start utility
(define-syntax-parameter Start
  (lambda (x) (error "Start syntax parameter can only be used in loop macro")))
(define-syntax with-start
  (lambda (x)
    (syntax-case x ()
    ((_ code ...)
     (with-syntax ((s (datum->syntax #'1 
				     (gensym "Start"))))
          #'(syntax-parameterize ((Start (lambda (x) #'s))) code ...))))))

;; end utility
(define (with-end stx a _ b)
  (syntax-case stx (if)
    ((if #f #f) a)
    (_          b)))

(begin
  (define-syntax-class compound-form
    (pattern (_ . _)))

  (define-splicing-syntax-class named-clause
    #:no-delimit-cut
    (pattern (~seq (~optional (~seq (~datum named) ~! name)) ...)
      #:attr code 
      (lambda (cc)
	(with-syntax ((name (if name 
				name
				(stx-gen #'1 "block"))))
	    #`(block name #,cc)))))

  (define-splicing-syntax-class main-clause
    (pattern (~or x:termination-test
		  x:unconditional
		  x:accumulation
		  x:conditional
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
	     #:attr body (lambda (cc)
			   (case (D #'type)
			     ((do doing)
			      #`(begin xx ... #,cc))
			     ((return)
			      #`(return ff2))))
	     #:attr inc  (lambda (cc) cc)
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
		    x
		    (~optional (~seq (~datum into) ~! v)) ...)
	     
	     #:with acc  (stx-gen #'1 "acc")
	     #:with X    #'x
	     #:with var  (if v v #'acc)	     		
	     #:attr init (lambda (cc) 
			   #`(let ((var '())) #,cc))
	     
	     #:attr body (lambda (cc)
			   #`(begin (set! var (cons X var))
				      #,cc))

	     #:attr inc (lambda (cc) cc)

	     #:attr end  (lambda (cc)
			   (let ((final (case (syntax->datum #'name)
					  ((collect collecting)
					   #'(reverse var))
					  ((append appending)
					   #'(append-all var))
					  ((nconc nconcing)
					   #'(append-all! var)))))
			     (with-end cc 
				       final
				       #:else
				       #`(begin (set! var #,final) 
						#,cc))))))
  

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
	   #:with Y  #'x
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
	   (lambda (cc)
	     (case (D #'type)
	       ((count counting)
		#`(begin (when x (set! X (+ X 1))) #,cc))
	       ((sum summing)
		#`(begin (set! X (+ X Y)) #,cc))
	       ((maximize maximizing)
		#`(begin (when (> Y X) (set! X x)) #,cc))
	       ((minimize minimizing)
		#`(begin (when (< Y X) (set! X x)) #,cc))))

	   #:attr inc (lambda (cc) cc)
	   #:attr end 
	   (lambda (cc)
	     (with-end cc #'X #:else cc))))

  (define-syntax sif
    (syntax-rules (unless)
      ((_ unless a b c) (if a c b))
      ((_ _      a b c) (if a b c))))

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

	     #:attr body (lambda (cc)
			   #`(let ((it f))
			       #,(if e.body
				     #`(sif type it
					   #,(1-apply 
					      (cons xsel.body xs.body) cc)
					   #,(1-apply 
					      (cons e.body    es.body) cc))
				     #`(sif type it 
					   #,(1-apply (cons xsel.body xs.body) 
						      cc)
					   #,cc))))
			       
				 
	     #:attr inc  (lambda (x) x)
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

	 #:attr body (lambda (cc)
		       (case (D #'type)
			 ((while)
			  #`(if f1 #,cc (finish)))
			 ((until)
			  #`(if f1 (finish) #,cc))
			 ((repeat)
			  #`(if (< i n) 
				(begin (set! i (+ i 1)) #,cc) 
				(finish)))
			 ((always)
			  #`(let ((it f1)) (if it #,cc (return #f))))
			 ((never)
			  #`(let ((it f1)) (if it (return #f) #,cc)))
			 ((thereis)
			  #`(let ((it f1)) (if it (return it) #,cc)))))

	 #:attr inc  (lambda (cc) cc)
	 #:attr end  (lambda (cc)
		       (case (D #'type)
			 ((while until repeat) cc)
			 ((always never)       (with-end cc #t #:else cc))
			 ((thereis)            (with-end cc #f #:else cc))))))


  (define-splicing-syntax-class variable-clause
    #:no-delimit-cut
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
	 #:attr body (lambda (x) x)
	 #:attr inc  (lambda (x) x)
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
			       (fluid-ref *initially*))))
		 ((finally)
		  (fluid-set! *finally* 
			      (cons
			       (lambda (cc) #`(begin x ... #,cc))
			       (fluid-ref *finally*)))))
	       (lambda (x) x))

	     #:attr body (lambda (x) x)
	     #:attr inc  (lambda (x) x)
	     #:attr end  (lambda (x) x)))



  (define-splicing-syntax-class for-as-clause
    #:no-delimit-cut
    (pattern (~seq (~or (~datum for) (~datum as)) ~! v
		   x-for:for-as-subclause
		   (~seq (~datum and) ~! vv xs:for-as-subclause) ...)
	 #:with (y  ...) (cons #'v #'(vv ...))
	 #:with ((qq ...) (ss ...) (zz ...))
	 (pattern->vars (cons #'v #'(vv ...)))

	 #:attr init 
	 (lambda (cc) 
	   #`(let ((zz #f) ... (ss #f) ...)
	       #,(1-apply (map (lambda (x v) (x v))
			       (cons x-for.init xs.init) 
			       #'(y  ...))
			  cc)))

	 #:attr body (lambda (cc)
		       (1-apply (map (lambda (x w) (x w))
				     (cons x-for.body xs.body)
				     #'(qq  ...))
				#`(begin (set! zz ss) ...
					 #,cc)))
	 
	 #:attr inc  (lambda (cc) 
		       (1-apply (map (lambda (x w) (x w))
				     (cons x-for.inc xs.inc)
				     #'(y ...))
				cc))
			
	 #:attr end  (lambda (cc) cc)))

  (define-splicing-syntax-class for-as-subclause
    #:no-delimit-cut
    (pattern (~or x:for-as-in/on-list
		  x:for-as-equals-then
		  x:for-as-across
		  x:for-as-hash
		  x:for-as-package
		  x:for-as-arithmetic)
		  
	      
	 
	 #:attr init x.init
	 #:attr body x.body
	 #:attr inc  x.inc
	 #:attr end  x.end))

  (define (check-identifier f)
    (lambda (v)
      (if (identifier? v)
	  (f v)
	  (error "Loop macro does not support destructuring for this clause"))))

  (define-splicing-syntax-class for-as-arithmetic
    #:no-delimit-cut
    (pattern (~or x:arithmetic-up
		  x:arithmetic-downto
		  x:arithmetic-downfrom)
	     #:attr init x.init
	     #:attr body (check-identifier x.body)
	     #:attr inc  x.inc
	     #:attr end  x.end))

  
  (define-splicing-syntax-class arithmetic-up
    #:no-delimit-cut
    (pattern (~seq (~or (~optional (~seq (~or (~datum from) 
					      (~datum upfrom)) 
					 f1-up))
			(~optional (~seq (~and type-up 
					       (~or (~datum to)
						    (~datum upto)
						    (~datum below)))
					 f2-up))
			(~optional (~seq (~datum by) f3-up)))
		   ...)
	#:fail-when (not (or f1-up f2-up f3-up))
	"'Arithmetic up' for-clause malformed"

	#:with vv (stx-gen #'1 "n")
	#:attr init
	(lambda (v)
	  (lambda (cc)
	    (if f1-up
		#`(let ((vv #,f1-up)) #,cc)
		#`(let ((vv 0))       #,cc))))

	#:with less (if (and type-up (eq? (D type-up) 'below))
			#'<
			#'<=)
		       
	#:attr body
	(lambda (v)
	  (lambda (cc)
	    (if f2-up
		#`(if (less vv #,f2-up) (let ((#,v vv)) #,cc) (finish))
		cc)))

	#:attr inc
	(lambda (v)
	  (lambda (cc)
	    (if f3-up
		#`(catch #t
			 (lambda () (set! vv (+ #,f3-up vv)) #,cc)
			 (lambda z (finish)))
		#`(begin (set! vv (+ vv 1)) #,cc))))

	#:attr end (lambda (v) (lambda (cc) cc))))

  (define-splicing-syntax-class arithmetic-downto
    #:no-delimit-cut
    (pattern (~seq (~or (~once    (~seq (~datum from) ~! f1))
			(~once    (~seq (~and type (~or (~datum downto)
							(~datum above)))
					 ~! f2))
			(~optional (~seq (~datum by) f3))) ...)
	#:with vv (stx-gen #'1 "n")
	#:with init
	(lambda (v)
	  (lambda (cc)
	    #`(let ((vv f1)) #,cc)))

	#:with grt (if (eq? (D #'type) 'above)
			#'>
			#'>=)
		       
	#:with body
	(lambda (v)
	  (lambda (cc)
	    #`(if (grt vv f2) (let ((#,v vv)) #,cc) (finish))))

	#:with inc
	(lambda (v)
	  (lambda (cc)
	    (if f3
		#`(catch #t
			 (lambda () (set! vv (- vv #,f3)) #,cc)
			 (lambda z (finish)))
		#`(begin (set! vv (- vv 1)) #,cc))))

	#:attr end (lambda (v) (lambda (cc) cc))))


  (define-splicing-syntax-class arithmetic-downfrom
    #:no-delimit-cut
    (pattern (~seq (~or (~once (~seq (~datum downfrom) ~! f1))
			(~optional (~seq (~and type (~or (~datum to)
							 (~datum downto)
							 (~datum above)))
					 f2))
			(~optional (~seq (~datum by) f3))) ...)
	#:with vv (stx-gen #'1 "n")
	#:with init
	(lambda (v)
	  (lambda (cc)
	    #`(let ((vv f1)) #,cc)))

	#:with grt (if (and type (eq? (D #'type) 'above))
			#'>
			#'>=)
		       
	#:with body
	(lambda (v)
	  (lambda (cc)
	    (if type
		#`(if (grt vv #,f2) (let ((#,v vv)) #,cc) (finish))
		cc)))
	  

	#:with inc
	(lambda (v)
	  (lambda (cc)
	    (if f3
		#`(catch #t
			 (lambda () (set! vv (- vv #,f3)) #,cc)
			 (lambda z (finish)))
		#`(begin (set! vv (- vv 1)) #,cc))))

	#:attr end (lambda (v) (lambda (cc) cc))))


  (define-splicing-syntax-class for-as-in/on-list
    #:no-delimit-cut
    (pattern (~seq (~and kind (~or (~datum in) (~datum on))) ~! f1 
		   (~optional (~seq (~datum by) ~! f2)) ...)
	     #:with li (stx-gen #'1 "li")
	     #:with loop   (datum->syntax #'v (gensym "loop"))
	     #:attr car-li 
	     (lambda ()
	       (case (syntax->datum #'kind)
		 ((in) #`(car li))
		 ((on) #'li)))

	     #:attr update 
	     (lambda ()
	       (if f2
		   #`(catch #t
			    (lambda () (set! li (#,f2 li)) (loop))
			    (lambda x (finish)))
		   #`(begin (set! li (cdr li)) (loop))))

	     #:attr init 	     
	     (lambda (v)
	       (lambda (cc) 
		 #`(let ((li f1)) #,cc)))

	     #:attr body 
	     (lambda (v)
	       (lambda (cc) 
		 #`(let loop ()
		     (if (*list-end-test* li)
			 (match #,(car-li)
				(#,v #,cc)
				(_ #,(update)))
			 (finish)))))

	     #:attr inc  
	     (lambda (v)
	       (lambda (cc)	       
		 (if f2
		     #`(catch #t
			      (lambda ()
				(set! li (#,f2 li)) #,cc)
			      (lambda x (finish)))
		     #`(begin (set! li (cdr li)) #,cc))))

	     #:attr end  (lambda (x) x)))
  
  (define-splicing-syntax-class for-as-equals-then
    #:no-delimit-cut
    (pattern (~seq (~datum =) ~! f1 
		   (~optional (~seq (~datum then) f2)) ...)
	     
	     #:with cont (stx-gen #'v "cont")	     
	     #:attr init 
	     (lambda (v)
	       (unless (identifier? v)
		       (error 
			(format 
			 #f
			 "equals then iterator only binds a identifier, not ~a" 
			 (syntax->datum v))))
	       (lambda (cc) cc))
		 
	     
	     #:attr body
	     (lambda (v)
	       (lambda (cc) 
		 #`(let ((#,v (if Start f1 #,(if f2 f2 v))))
		     #,cc)))


	     #:attr inc
	     (lambda (v)
	       (lambda (cc) cc))

	     #:attr end  
	     (lambda (x) x)))

  (define-syntax-rule (mk-seq for-as-across across generalized-vector-length
			      generalized-vector-ref)

    (define-splicing-syntax-class for-as-across
      #:no-delimit-cut
      (pattern (~seq (~datum across) ~! f1)
	       #:with ar   (stx-gen #'v "array")
	       #:with ar-n (stx-gen #'v "n")
	       #:with ar-i (stx-gen #'v "i")
	       #:attr init 
	       (lambda (v)
		 (lambda (cc)
		   #`(let* ((ar   f1) 
			    (ar-i 0) 
			    (ar-n (generalized-vector-length ar))) 
		       #,cc)))

	       #:attr body
	       (lambda (v)
		 (lambda (cc) 
		   #`(let loop ()
		       (if (< ar-i ar-n)
			   (match (generalized-vector-ref ar ar-i)
				  (#,v #,cc)
				  (_ (set! ar-i (+ ar-i 1)) (loop)))
			   (finish)))))

	       #:attr inc  
	       (lambda (v)
		 (lambda (cc)
		   #`(begin (set! ar-i (+ ar-i 1)) #,cc)))
	       
	       #:attr end  (lambda (x) x))))

  (mk-seq for-as-across across generalized-vector-length generalized-vector-ref)

  (define-splicing-syntax-class for-as-hash
    #:no-delimit-cut
    (pattern (~seq (~datum being)
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


	     #:with loop (stx-gen #'1 "loop")
	     #:with li   (stx-gen #'1 "li")
	     #:attr p-key 
	     (lambda (v)
	       (case (D #'type)
		 ((hash-key hash-keys)
		   v)
		 ((hash-value hash-values)
		  (if ov ov #'_))))

	     #:attr p-value 
	     (lambda (v)
	       (case (D #'type)
		 ((hash-key hash-keys)
		  (if ov ov #'_))
		 ((hash-value hash-values)
		  v)))
		
	     #:attr init 
	     (lambda (v)
	       (lambda (cc)
		 #`(let ((li (hash-map->list cons ht))) #,cc)))

	     #:attr body 
	     (lambda (v)
	       (lambda (cc)
		 #`(let loop ()
		     (if (pair? li)
			 (match (car li)
				((#,(p-key v) . #,(p-value v))
				 #,cc)
				(_ 
				 (set! li (cdr li))
				 (loop)))
			 (finish)))))
			   
	     #:attr inc
	     (lambda (li)
	       (lambda (cc)
		 #`(begin (set! li (cdr li)) #,cc)))

	     #:attr end  
	     (lambda (x) x)))


  (define-splicing-syntax-class for-as-package
    #:no-delimit-cut
    (pattern (~seq (~datum being)
		   (~or (~datum symbol) (~datum symbols)
			(~datum present-symbol)
			(~datum present-symbols)
			(~datum external-symbol)
			(~datum external-symbols)) ~!
		   (~optional (~seq (~or (~datum in) (~datum of))
				    p)) ...)
	     #:attr init (lambda x (error "for as package is not imlpemented"))
	     #:attr body (lambda (f x) x)
	     #:attr inc  (lambda (f x) x)
	     #:attr end  (lambda (x) x))))
		
(define-syntax loop
  (lambda (x)
    (syntax-parse x
      ((_ (~do (fluid-set! *finally* '()) (fluid-set! *initially* '()))
	  nm:named-clause v:variable-clause ... m:main-clause ...)
	(with-syntax
	 ((loop  (datum->syntax #'1 (gensym "loop")))
	  (it    (datum->syntax #'1 (gensym "it")))
	  (ret   (datum->syntax #'1 (gensym "ret"))))
	 #`(let ()
	     #,(nm.code
		(1-apply (append v.init m.init (reverse 
						(fluid-ref *initially*)))
		   #`(with-finally
		      (with-it
		       (let ((it #f))
		        (with-start		       			 
		         (let loop ((Start #t))
			  #,(1-apply (append v.body m.body)
				     (1-apply v.inc #'(loop #f)))))))

		      (let ((ret #,(1-apply (append v.end m.end) #'(if #f #f))))
			#,(1-apply (reverse (fluid-ref *finally*))
				   #'ret)))))))))))

(define-syntax debug-loop
  (lambda (x)
    (debug-parse x
      (_ (~do (fluid-set! *finally* '()) (fluid-set! *initially* '()))
	 nm:named-clause v:variable-clause ... m:main-clause ...))))
