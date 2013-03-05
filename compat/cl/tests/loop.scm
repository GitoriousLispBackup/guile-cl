(use-modules (ice-9 pretty-print))
(use-modules (compat cl loop))

(define-syntax-rule (test x y)
  (let ((xx x) (yy y))
    (if (equal? xx yy)
	(pretty-print '(----> OK))
	(pretty-print `((x ----> FAAAAAAAAAAAIL) (,xx != ,yy))))))

(test (loop for i upto 10 collect i) 
      '(0 1 2 3 4 5 6 7 8 9 10))

(test (loop for i from 0 downto -10 collect i)
      '(0 -1 -2 -3 -4 -5 -6 -7 -8 -9 -10))

(test (loop for i in (list 10 20 30 40) collect i) 
      '(10 20 30 40))

(test (loop for i in (list 10 20 30 40) by cddr collect i)
      '(10 30))

(test (loop for x on (list 10 20 30) collect x)
      '((10 20 30) (20 30) (30)))

(test (loop for x on (list 10 20 30 40) by cddr collect x)
      '((10 20 30 40) (30 40)))

(test (loop for x across "abcd" collect x) 
      '(#\a #\b #\c #\d))

(test (loop repeat 5 
	    for x = 0 then y
	    for y = 1 then (+ x y)
	    collect y)
      '(1 2 4 8 16))

(test (loop repeat 5
	    for y = 1 then (+ x y)
	    for x = 0 then y
	    collect y)
      '(1 1 2 4 8))

(test (loop repeat 5 
	    for x = 0 then y
	    and y = 1 then (+ x y)
	    collect y)
      '(1 1 2 3 5))

(test (loop for (a b) in '((1 2) (3 4) (5 6))
            collect (format #f "a: ~a; b: ~a" a b))
      '("a: 1; b: 2"
	"a: 3; b: 4"
	"a: 5; b: 6"))

(test (with-output-to-string
       (lambda ()
	 (loop for (item . rest) on '(1 2 3)
	       do (format #t "~a" item)
	       when (pair? rest) do (format #t ", "))))
      "1, 2, 3")

(test (loop for (a _) in '((1 2) (3 4) (5 6)) collect a)
      '(1 3 5))

(define *random* (iota 100))
(test (loop for i in *random*
	    counting   (even? i) into evens
	    counting   (odd? i)  into odds
	    summing    i         into total
	    maximizing i         into max
	    minimizing i         into min
	    finally (return (list min max total evens odds)))
      '(0 99 4950 50 50))


(test (loop for i from 1 to 10 when (even? i) sum i)
      30)

(test (loop for i from 1 to 100
	    if (even? i)
	       minimize i into min-even and 
	       maximize i into max-even and
	       unless (zero? (modulo i 4))
	         sum i into even-not-fours-total
               end
               and sum i into even-total
            else
               minimize i into min-odd and
               maximize i into max-odd and
               when (zero? (modulo i 5)) 
                  sum i into fives-total
               end
               and sum i into odd-total
            finally 
	       (return (list min-even
			     max-even
			     min-odd
			     max-odd
			     even-total
			     odd-total
			     fives-total
			     even-not-fours-total)))
      '(2 100 1 99 2550 2500 500 1250))


(test (loop for n in '(2 4 6) always (even? n))
      #t)
(test (loop for n in '(2 3 6) always (even? n))
      #f)

(test (loop for n in '(2 4 6) never (odd? n))
      #t)

(test (loop for n in '(2 3 6) never (odd? n))
      #f)

(test (loop for char across "abc123" thereis (char-numeric? char))
      #t)

(test (loop for char across "abcdef" thereis (char-numeric? char)) 
      #f)