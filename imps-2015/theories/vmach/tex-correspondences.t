(define (PRESENT-TEX-LAMBDA-ABSTRACTION formatter op args bp)
  (ignore bp)
  (if (<= (maximum-nesting-for-logical-expressions) 0)
      `(    " [ \\," 

	    ,(present-tex-parameter-list (car args))
	    " \\, " " \\mapsto " " \\, "

	    ,(present-tree formatter (cadr args) 0)

	    "\\, ] ")
      (bind (((maximum-nesting-for-logical-expressions)
	      (-1+ (maximum-nesting-for-logical-expressions)))
	     ((current-indentation)
	      (string-append (current-indentation) "XX")))
	`(    " [ \\," 

	      ,(present-tex-parameter-list (car args))
	      " \\, " " \\mapsto " 	    
	      ,(present-tree formatter (cadr args) 0)
	    
	      "\\, ] "))))

(make-presentation-format *tex-form* 'lambda " \\lambda "   
			  present-tex-lambda-abstraction 50)

(define (PRESENT-TEX-RAISE formatter op args bp)
  (ignore bp)
  `(
    ,(present-tree formatter (cadr args) 0)
    ,(presentation-format formatter op)
    \{
    \[
    ,(present-tree formatter (car args) 0)
    \]
    \}))

(def-print-syntax raise
  tex
  (token ^)
  (method PRESENT-TEX-RAISE)
  (binding 160))  
  

(make-tex-correspondence "default" "{\\delta}")
(make-tex-correspondence 'offset "{\\eta}")
(make-tex-correspondence "ind" "{\\bf I}")
(make-tex-correspondence "aa" "{\\bf A}")
(make-tex-correspondence "bb" "{\\bf B}")
(make-tex-correspondence "place" "{\\cal P}")
(make-tex-correspondence 'mem%obj "{\\cal M}")
(make-tex-correspondence "word" "{\\cal W}")
(make-tex-correspondence "istate" "{\\Omega}")
(make-tex-correspondence "twist" "{\\Delta}")
(make-tex-correspondence 'bound%place "{{\\cal P}_{\\bf B}}")
(make-tex-correspondence 'regular%place "{{\\cal P}_{\\bf R}}")
(make-tex-correspondence 'bound%mem "{{\\cal M}_{\\bf B}}")
(make-tex-correspondence "source" "{\\Phi}")

(let ((generic-files '(iterate  iterate-supplements))
      (specific-files '(iterate-lemmas places machines)))

  (let ((files
	 (append (map (lambda (x) (list 'imps (symbol-append 'theories/generic-theories/ x))) generic-files)
		 (map (lambda (x) (list 'imps (symbol-append 'theories/vmach/ x))) specific-files))))
    (build-tex-multifile-document files  "/tmp/cow")))
