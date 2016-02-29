; Copyright (c) 1990-1997 The MITRE Corporation
; 
; Authors: W. M. Farmer, J. D. Guttman, F. J. Thayer
;   
; The MITRE Corporation (MITRE) provides this software to you without
; charge to use, copy, modify or enhance for any legitimate purpose
; provided you reproduce MITRE's copyright notice in any copy or
; derivative work of this software.
; 
; This software is the copyright work of MITRE.  No ownership or other
; proprietary interest in this software is granted you other than what
; is granted in this license.
; 
; Any modification or enhancement of this software must identify the
; part of this software that was modified, by whom and when, and must
; inherit this license including its warranty disclaimers.
; 
; MITRE IS PROVIDING THE PRODUCT "AS IS" AND MAKES NO WARRANTY, EXPRESS
; OR IMPLIED, AS TO THE ACCURACY, CAPABILITY, EFFICIENCY OR FUNCTIONING
; OF THIS SOFTWARE AND DOCUMENTATION.  IN NO EVENT WILL MITRE BE LIABLE
; FOR ANY GENERAL, CONSEQUENTIAL, INDIRECT, INCIDENTAL, EXEMPLARY OR
; SPECIAL DAMAGES, EVEN IF MITRE HAS BEEN ADVISED OF THE POSSIBILITY OF
; SUCH DAMAGES.
; 
; You, at your expense, hereby indemnify and hold harmless MITRE, its
; Board of Trustees, officers, agents and employees, from any and all
; liability or damages to third parties, including attorneys' fees,
; court costs, and other related costs and expenses, arising out of your
; use of this software irrespective of the cause of said liability.
; 
; The export from the United States or the subsequent reexport of this
; software is subject to compliance with United States export control
; and munitions control restrictions.  You agree that in the event you
; seek to export this software or any derivative work thereof, you
; assume full responsibility for obtaining all necessary export licenses
; and approvals and for assuring compliance with applicable reexport
; restrictions.
; 
; Emulation of TEA in Common Lisp for IMPS: Author F. J. Thayer.
; 
; 
; COPYRIGHT NOTICE INSERTED: Wed Mar  5 13:36:30 EST 1997


(in-package "TEA-IMPLEMENTATION")

(eval-when (compile eval load)
  (defun prognify (x)
    (cond ((atom x) 'nil)
	  ((atom (cdr x)) (car x))
	  (t `(progn ,@x))))

;;from T sources.

(defmacro destructure (specs &rest body)
  (labels ((expand-destructure 
	    (specs body)
	    (let ((a '()) (b '()))
	      (mapc #'(lambda (spec)
			(flet ((foo (vars z val)
				    (cond ((null vars))
					  ((atom  vars)
					   (push `(,vars (,z ,val)) a))
					  (t
					   (let ((temp (generate-symbol)))
					     (push `(,temp (,z ,val)) a)
					     (push `(,vars ,temp) b))))))  
			  (let ((vars (car spec)) (val (cadr spec)))
			    (cond ((atom vars)
				   ;; No destructuring called for; just do as for LET.
				   (push spec a))
				  ((consp val)
				   ;; RHS is a call or special form; need to stow value.
				   (let ((temp (generate-symbol)))
				     (push  `(,temp ,val) a)
				     (push  `(,vars ,temp) b)))
				  (t
				   (foo (car vars) 'car val)
				   (foo (cdr vars) 'cdr val))))))
		    specs)
	      `(let ,(nreverse a)
		 ,@(cond ((null b) body)
			 (t (list (expand-destructure (nreverse b) body))))))))
    (expand-destructure specs body)))

(defmacro select (key . clauses)
  (flet ((lose (clause)
	       (error "bad ~S clause syntax: ~S"
		      'select
		      clause)))
    (flet ((expand-select (keyvar clauses)
			  (mapcar #'(lambda (clause)
				      (cond ((atom clause) (lose clause))
					    ((listp (car clause))
					     `((or
						,@(mapcar #'(lambda (k) `(eq ,keyvar ,k))
							  (car clause)))
					       ,@(cdr clause)))
					    ((eq (car clause) 'tea::else) 
					     `(t ,@(cdr clause)))
					    (t (lose clause))))
				  clauses)))

      (let ((keyvar (generate-symbol)))
	`(let ((,keyvar ,key))
	   (cond ,@(expand-select keyvar clauses)))))))


(defmacro tea::case (key . clauses)
  (flet ((lose (clause)
	       (error "bad ~S clause syntax: ~S"
		      'select
		      clause)))
    (flet ((expand-case (keyvar clauses)
			  (mapcar #'(lambda (clause)
				      (cond ((atom clause) (lose clause))
					    ((listp (car clause))
					     `((or
						,@(mapcar #'(lambda (k) `(eq ,keyvar ',k))
							  (car clause)))
					       ,@(cdr clause)))
					    ((eq (car clause) 'tea::else) 
					     `(t ,@(cdr clause)))
					    (t (lose clause))))
				  clauses)))

      (let ((keyvar (generate-symbol)))
	`(let ((,keyvar ,key))
	   (cond ,@(expand-case keyvar clauses)))))))


(defmacro tea::cond (&rest clauses)
  (let ((block-name (generate-symbol)))
    (flet ((expand-cond 
	    (clauses)
	    (mapcar #'(lambda (clause)
			(if (eq (cadr clause) 'tea::=>)
			    (let ((var (generate-symbol)))
			      `((let ((,var ,(car clause)))
				  (if ,var
				      (return-from ,block-name
					(funcall ,(caddr clause) ,var))
				    '()))))
			  clause))
		    clauses)))
      `(block ,block-name (cond ,@(expand-cond clauses))))))

(defmacro tea::push (location val)
  `(tea::set ,location (cons ,val ,location)))
;;  `(push ,val ,location))

(defmacro tea::pop (location)
  `(pop ,location))

(defmacro tea::receive (vars values-form &rest body) 
  (let ((ignored nil)
	(declared nil))
    (setq vars
	    (mapcar #'(lambda (x) 
			(if (null x) 
			    (progn
			      (setq x (generate-symbol))
			      (push x ignored)
			      x)
			  x))
		vars))
    (setq declared 
	  (if ignored
	      `((declare (ignore ,@ignored)))
	    `()))
  `(multiple-value-bind ,vars ,values-form ,@declared ,@body)))

(defmacro tea::return (&rest vals)
  `(values ,@vals))


(defmacro tea::block (&rest forms)
  `(progn ,@forms))

(defmacro tea::block0 (&rest forms)
  `(prog1 ,@forms))

(defmacro tea::iterate (name specs . body)
  (let ((vars (mapcar #'car specs))
	(init-values (mapcar #'cadr specs)))
    `(labels-1 (((,name ,@vars) ,@body)) (,name ,@init-values))))

(defmacro pset (&rest init-forms)
  (let ((forms (do ((l init-forms (cddr l))
		    (pairs nil (cons (list (car l) (cadr l)) pairs)))
		   ((null l) pairs))))
    (let ((temps (mapcar #'(lambda (x) (declare (ignore x)) (generate-symbol)) forms)))
      `(let ,(mapcar #'(lambda (x y) (list x (cadr y))) temps forms)
	 ,@(mapcar  #'(lambda (y x) `(tea::set ,(car y) ,x)) forms temps)))))

(defmacro tea::bind (specs &rest body)
  (let ((locs (mapcar #'car specs))
	(saved-vals (mapcar #'(lambda (x) (declare (ignore x)) (generate-symbol)) specs))
	(init-values (mapcar #'cadr specs)))

    `(let ,(mapcar #'(lambda (x y) (list x y)) saved-vals locs)
       (unwind-protect
	   (progn
	     (pset ,@(mapcan #'(lambda (x y) (list x y)) locs init-values))
	     ,@body)
	 (pset ,@(mapcan #'(lambda (x y) (list x y)) locs saved-vals))))))
	 
;;(eval-when (compile eval load)
(defun expand-star-macro (specs body macro-name)
    (cond ((null (cdr specs))
	   `(,macro-name ,specs ,@body))
	  (t `(,macro-name (,(car specs))
		       ,(expand-star-macro (cdr specs) body macro-name)))))

(defmacro tea::bind* (specs  &rest body)
  (expand-star-macro specs body 'bind))
	 
(defmacro tea::destructure* (specs &rest body)
  (expand-star-macro specs body 'destructure))

;(defmacro tea::ignore (&rest vars)
;  `(declare (ignore ,@vars)))

(defmacro tea::ignore (&rest vars) 't)

(defmacro tea::comment (&rest body)
  (declare (ignore body))
  `(progn 'tea::comment))

(defmacro tea::herald (&rest body)
  (declare (ignore body))
  `(progn 'tea::herald))

(defmacro tea::lambda (args &rest body)
  `(function (lambda ,@(destructure-args args) ,@body)))

;;		  "FLET" "LABELS"
(defmacro tea::labels (specs &rest body)
  (let* ((specs (mung-function-specs specs))
	 (var-specs (mapcar #'(lambda (x) `(,(car x) (function ,(car x))))
			    specs)))
    `(labels ,specs (let ,var-specs ,@body))))

(defmacro labels-1 (specs &rest body)
  `(labels ,(mung-function-specs specs) ,@body))

(defmacro tea::flet (specs &rest body)
    (let* ((specs (mung-function-specs specs))
	   (var-specs (mapcar #'(lambda (x) `(,(car x) (function ,(car x))))
			      specs)))
      `(flet ,specs (let ,var-specs ,@body))))

(defmacro tea::at-top-level (form)
  form)

(defun mung-function-specs (specs) ;;((f a) body)
  (mapcar #'(lambda (x)`(,(caar x) ,@(destructure-args (cdar x)) ,@(cdr x)))

	  ;;just leave it alone. Minimal error checking.

	  specs))

(defmacro tea::call-with-current-continuation (proc)
  (let ((tag (generate-symbol)))
    `(catch ',tag
       (funcall ,proc ',tag))))


(defmacro tea::increment (arg)
  `(tea::set ,arg (1+ ,arg)))


(defmacro tea::decrement (arg)
  `(tea::set ,arg (1- ,arg)))

(defmacro tea::swap (x new-value)
  `(progn
     (let ((old ,x))
       (tea::set ,x ,new-value)
       old)))

(defmacro tea::if (&rest args)
  `(if ,@args))

(defmacro tea::or (&rest args)
  `(or ,@args))

(defmacro tea::not (arg)
  `(not ,arg))

(defmacro tea::and (&rest args)
  `(and ,@args))
		  
)