;% Copyright (c) 1990-1994 The MITRE Corporation
;% 
;% Authors: W. M. Farmer, J. D. Guttman, F. J. Thayer
;%   
;% The MITRE Corporation (MITRE) provides this software to you without
;% charge to use, copy, modify or enhance for any legitimate purpose
;% provided you reproduce MITRE's copyright notice in any copy or
;% derivative work of this software.
;% 
;% This software is the copyright work of MITRE.  No ownership or other
;% proprietary interest in this software is granted you other than what
;% is granted in this license.
;% 
;% Any modification or enhancement of this software must identify the
;% part of this software that was modified, by whom and when, and must
;% inherit this license including its warranty disclaimers.
;% 
;% MITRE IS PROVIDING THE PRODUCT "AS IS" AND MAKES NO WARRANTY, EXPRESS
;% OR IMPLIED, AS TO THE ACCURACY, CAPABILITY, EFFICIENCY OR FUNCTIONING
;% OF THIS SOFTWARE AND DOCUMENTATION.  IN NO EVENT WILL MITRE BE LIABLE
;% FOR ANY GENERAL, CONSEQUENTIAL, INDIRECT, INCIDENTAL, EXEMPLARY OR
;% SPECIAL DAMAGES, EVEN IF MITRE HAS BEEN ADVISED OF THE POSSIBILITY OF
;% SUCH DAMAGES.
;% 
;% You, at your expense, hereby indemnify and hold harmless MITRE, its
;% Board of Trustees, officers, agents and employees, from any and all
;% liability or damages to third parties, including attorneys' fees,
;% court costs, and other related costs and expenses, arising out of your
;% use of this software irrespective of the cause of said liability.
;% 
;% The export from the United States or the subsequent reexport of this
;% software is subject to compliance with United States export control
;% and munitions control restrictions.  You agree that in the event you
;% seek to export this software or any derivative work thereof, you
;% assume full responsibility for obtaining all necessary export licenses
;% and approvals and for assuring compliance with applicable reexport
;% restrictions.
;% 
;% 
;% COPYRIGHT NOTICE INSERTED: Mon Apr 11 11:42:27 EDT 1994


(herald tabular)

(define (TABLE-OPERATOR-METHOD parser op)
  (prefix-operator-next-token-check parser op)

  (let ((match (if (eq? (next-token parser) '\()
		   '\)
		   '\})))
    (input-next-token parser)
    (let ((args (parse-matching-operator parser match)))
      (or (every? (lambda (x) (and (list? x)
				   (eq? (car x) 'left-french-bracket)))
		  (cdr args))
	  (report-error parser "Illegal bracketing of table indices or entries: use {."))
      (let ((args (cons (car args) (map cdr (cdr args)))))
	(let ((fn (car args))
	      (top (caddr args))
	      (side (cadr args))
	      (entries (cdddr args)))
	  (or (and (is-set? top) (is-set? side))
	      (report-error parser "Illegal table: non-unique indexing of entries."))
	  (let ((n (length top))
		(m (length side)))
	    (or (every? (lambda (x) (= (length x) n)) entries)
		(report-error parser "All rows in the table must have length ~a" n))
	    (or (= (length entries) m)
		(report-error parser "There must be exactly ~a rows in the table (not ~a)." m (length entries)))
	    (iterate outer ((n1 0) (expressions '()))

	      (if (= n n1)
		  `(and ,@expressions)
		  (let ((new
			 (iterate inner ((m1 0) (expressions expressions))

			   (if (= m m1)
			       expressions
			       (let ((table-entry (nth (nth entries m1) n1)))
				 (iNner (1+ m1) (if (eq? table-entry 'unspecified)
						    expressions
						    (cons `(= (,fn ,(nth side m1) ,(nth top n1))
							      ,table-entry)
							  expressions))))))))
		    (outer (1+ n1) new))))))))))


(define (PREFIX-METHOD-FB parser op)
  `(,(intermediate-format parser op) ,@(parse-matching-operator parser '\})))

(make-operator *parse* 'table 'table table-operator-method '() 160)

;;;Printing


(define (TABULAR-ENTRIES? args) ;;((= (f a b) c) ...)
  (let ((fn (and (list? args)
		 (list? (car args))
		 (list? (cadar args))
		 (not (null? (cadar args)))
		 (car (cadar args)))))

    (and fn
	 (every? (lambda (x) (and (list? x)
				  (eq? (car x) '=)
				  (eq? (car (cadr x)) fn)
				  (= (length (cadr x)) 3)))
		 args))))

(define (ARRANGE-TABLE formatter args)
  (let ((compare (lambda (a b) (< (tree-hash a) (tree-hash b)))))
    (let* ((fn (present-tree formatter (car (cadar args)) 0))
	   (side (sort (make-set (map cadadr args)) compare))
	   (formatted-side
	    (map-alternate-insert '\, (lambda (x) (present-tree formatter x 0)) side))
	   (top (sort (make-set (map (lambda (x) (caddr (cadr x))) args)) compare))
	   (formatted-top
	    (map-alternate-insert '\, (lambda (x) (present-tree formatter x 0)) top)))
      (let* ((reduced-entries (map (lambda (x) (cons (cdr (cadr x)) (caddr x))) args))
	     (entries
	      (map-alternate-insert
	       '\,
	       (lambda (s)
		 (list
		  " ~%   "
		  '\{
		  (map-alternate-insert
		   '\,
		   (lambda(t)
		     (let ((look-up (ass equal? (list s t) reduced-entries)))
		       (if look-up (present-tree formatter (cdr look-up) 0)
			   'unspecified)))
		   top) '\} ))
	       side)))
	(receive (left-delimiter right-delimiter)
	  (if (treat-qcs-specially?)
	      (return '\{ '\})
	      (return '\( '\)))
	  `(table ,left-delimiter ,fn \, "    " \{ ,formatted-side \} \, "   " \{ ,formatted-top \} \, "" ,entries ,right-delimiter))))))
      
  
(define (PRESENT-TABULAR-DATA formatter op args bp)
  (if (tabular-entries? args)
      (arrange-table formatter args)
      (present-nary-infix-operator formatter op args bp)))

(make-presentation-format *form* 'and " and "  present-tabular-data  60)	     

    
(define (ARRANGE-TEX-TABLE formatter args)
  (let ((compare (lambda (a b) (< (tree-hash a) (tree-hash b)))))
    (bind (((current-indentation) (string-append (current-indentation) "X")))
      (let* ((fn (present-tree formatter (car (cadar args)) 0))
	     (side (sort (make-set (map cadadr args)) compare))
	     (top (sort (make-set (map (lambda (x) (caddr (cadr x))) args)) compare))
	     (formatted-top
	      (map-alternate-insert  " & " (lambda (x) (present-tree formatter x 0)) top)))
	(let* ((reduced-entries (map (lambda (x) (cons (cdr (cadr x)) (caddr x))) args))
	       (entries
		(map-alternate-insert
		 " \\\\ \\hline "
		 (lambda (s)
		   (append
		    (list (present-tree formatter s 0) " & ")
		    (map-alternate-insert
		     " & "
		     (lambda(t)
		       (let ((look-up (ass equal? (list s t) reduced-entries)))
			 (if look-up (present-tree formatter (cdr look-up) 0)
			     " \\phantom{X} ")))
		     top)))
		 side)))	    
	  `( " \\newline  \\newline "
	     ,(format nil " \\phantom\{~a\} " (current-indentation))
	     " \\begin{array}{|c|| "
	     ,(alternate-insert
	       " | "
	       (replace-list-entries top " c "))
	     " |} "

	     " \\hline "
	 
	     ,fn
	 
	     " & "
	     ,formatted-top

	     " \\\\ \\hline \\hline "

	     ,entries 


	     " \\\\ "
	     " \\hline "
	     " \\end{array} "))))))


(define (PRESENT-TEX-TABULAR-DATA formatter op args bp)
  (if (tabular-entries? args)
      (arrange-tex-table formatter args)
      (present-tex-logical-operator formatter op args bp)))

(make-presentation-format *tex-form*
			  'and
			  (list "\{ \\rm conjunction \} "
				" \\wedge ")
			  present-tex-tabular-data 60)	


