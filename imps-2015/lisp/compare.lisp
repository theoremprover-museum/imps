(in-package "USER")

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

(in-package "USER")

;;Converts applications (f a b c d) to (funcall f a b c d) if f is lexically
;;within a binding of f.

(defvar advising-p nil)
(defvar notifications nil)
(defvar tea-package-name "TEA")
(defvar *package-form* '(in-package "TEA"))
(defvar *header-string* ";;;SOURCE file generated automatically.")
(defvar other-top-level-forms '(let let* block block0))
(defvar logport ()) ;;implicitly declare it special.

(defun notify (gravity &rest messages) 
  (format logport (string-upcase (format nil "~A: " gravity)))
  (apply #'format logport messages)
  (format logport "~%~%")
  (push (cons gravity messages) notifications))
;;;
(defun advise (expr_0 expr) expr)

;;;(defun advise (expr_0 expr)
;;;  (if advising-p
;;;      nil
;;;    (let ((advising-p 't))
;;;      (if (equal expr_0 expr)
;;;	  (format logport "No change in \"~A\" form.~%" (car expr_0))
;;;	(format logport "Changing~% ~S to~% ~S~%" expr_0 expr))
;;;      expr)))

(defun tag-variable (tag expr)
  (if (symbolp expr)
      (cons tag expr)
    nil))

(defun convert-top-level (expr)
  (wrap-top-levels (convert expr nil nil)))

(defun wrap-top-levels (expr)
  (if (and (listp expr) (member (car expr) other-top-level-forms))
      (progn (notify 'warning  "Top level ~A form~%" (car expr))
	     `(at-top-level ,expr))
    expr))

(defun convert (expr vars fns)
  (or (null (intersection vars fns)) (error "Confusing syntax"))
  (block cond-block
    (cond ((and (symbolp expr)
		(member (tag-variable 'is-labeled expr) fns :test #'equal))

	   (notify 'warning  

"Labels (or iterate) function specification in source code contains
reference to value of symbol being defined as function.")

	   (advise expr `(function ,expr)))

	  ((and (symbolp expr)
		(member (tag-variable 'catch expr) vars :test #'equal))
	   (notify 'serious-warning  

"Variable denotes continuation. Continuations not used. Converting to
catch with symbol. ")

	   (advise expr  `(quote ,expr)))

	  ((member (tag-variable 'is-reset expr) fns :test #'equal)

	   ;;This means expr is a variable within an FLET or LABELS
	   ;;that is reset somewhere else within that same flet or
	   ;;labels as a variable.  Use its value slot rather than its
	   ;;function slot. 

	   expr)

	  ((member expr fns)
	   (notify 'note 

"Function symbol ~A occurs in an argument evaluated position.  Check
it is bound as a variable by a surrounding labels or flet." expr)	    

	   `(function ,expr))
	  ((atom expr) 
	   expr)
	  ((member (car expr) vars)
	   (advise expr `(funcall ,(car expr) ,@(convert-list (cdr expr) vars fns))))
	  ((member (tag-variable 'is-reset (car expr)) fns :test #'equal)

	   ;;This means (car expr) is a variable within an flet or
	   ;;labels that is reset somewhere else within that same flet
	   ;;or labels as a variable.  Use its value slot then rather than its fucntion 
	   ;;slot.

	   (advise expr `(funcall ,(car expr) ,@(convert-list (cdr expr) vars fns))))
	  ((member (tag-variable 'catch (car expr)) vars :test #'equal)
	   
	   ;This means variables occurs within the scope of a catch. The tag is now
	   ;a symbol rather than a continuation. The symbol chosen is the symbol
	   ;used to refer to the continuation.

	   (advise expr `(throw ',(car expr) ,@(convert-list (cdr expr) vars fns))))
	  ((*value-form-call-p expr)
	   (convert-list expr vars fns))
	  ((listp (car expr)) 
	   (advise expr `(funcall ,@(convert-list expr vars fns))))
	  ((let ((handler (dispatch-handler (car expr))))
	     (if handler
		 (return-from cond-block (funcall handler expr vars fns))
	       nil)))
	  (t `(,(car expr) ,@(convert-list (cdr  expr) vars fns))))))

(defun convert-list (l vars fns)
  (mapcar #'(lambda (x) (convert x vars fns)) l))

(defun *value-form-call-p (expr)
  (and (listp (car expr)) 
       (is-form-p '*value (car expr))))

(defvar dispatch-handler-alist '())

(defun dispatch-handler (expr)
  (cdr (assoc expr dispatch-handler-alist)))

(defun add-handler (name handler)
  (setq dispatch-handler-alist
	(cons (cons name handler)  dispatch-handler-alist)))

(mapcar #'(lambda (x) (add-handler (car x) (cadr x)))
	'((define  define-handler)
	  (*define *define-handler)
	    (define-operation   define-handler)
	    (define-predicate define-handler)
	    (define-integrable define-handler)
	    (define-settable-operation define-handler)
	    (define-syntax  define-handler)
	    (define-structure-type deftype-handler)
	    (lambda lambda-handler)
	    (cond cond-handler)
	    (xcond cond-handler)
	    (case case-handler)
	    (xcase case-handler)
	    (eval eval-handler)
	    (labels labels-handler)
	    (let let-handler)
	    (do do-handler)
	    (destructure destructure-handler)
	    (destructure* let*-handler-strict)
	    (bind bind-handler)
	    (catch catch-handler)
	    (receive receive-handler)
	    (with-open-ports let-handler)
	    (let* let*-handler-strict)
	    (object object-handler)
	    (operation object-handler)
	    (iterate iterate-handler)
	    (comment comment-handler)
	    (herald herald-handler)
	    (*require require-handler)
	    (load load-handler)
	    (select select-handler)
	    (set set-handler)
	    (lset lset-handler)
	    (*value *value-handler)
	    (quote quote-handler)))	   

(defun is-form-p (form expr)
  (and (listp expr)
       (eq (car expr) form)))

(defun cond-handler (expr vars fns)
  `(cond ,@(mapcar #'(lambda (x)(convert-list x vars fns)) (cdr expr))))

(defun select-handler (expr vars fns)
  `(,(car expr)
    ,(convert (cadr expr) vars fns)
    ,@(mapcar #'(lambda (x)
		  `(,(if (atom (car x))
			 (convert (car x) vars fns)
		       (convert-list (car x) vars fns))
		    ,@(convert-list (cdr x) vars fns)))
	      (cddr expr))))

(defun case-handler (expr vars fns)
  `(case
    ,(convert (cadr expr) vars fns)
    ,@(mapcar #'(lambda (x)
		  `(,(car x)
		    ,@(convert-list (cdr x) vars fns)))
	      (cddr expr))))

(defun set-handler (expr vars fns)
  (if (and (member (cadr expr) fns) 
	   (not (member  (tag-variable 'is-reset (cadr expr)) fns :test #'equal)))
      (progn
	(notify 'serious-warning 

"Function variable \"~A\" which occurs within scope of labels or flet
special form is reset. Program will redo the labels or flet to change
uses of this symbol as function in the lexical environment and change
them to \"FUNCALL ~A\"."

		(cadr expr) 
		(cadr expr))
	(throw 'redo (tag-variable 'is-reset (cadr expr)))) 
    `(,(car expr) ,@(convert-list (cdr expr) vars fns))))


(defun quote-handler (expr vars fns)
  (if (null (cadr expr)) (cadr expr)
    `(quote ,@(cdr expr))))

(defun load-handler (expr vars fns)
  `(load ,(cadr expr)))

(defun catch-handler (expr vars fns)
  (notify 'note "Catch form with tag ~A. Quoting TAG expression." (cadr expr))
  (or (symbolp (cadr expr))
      (notify 'very-serious-warning "Catch tag ~A is not a symbol!" (cadr expr)))
  `(catch ',(cadr expr) 
     ,@(convert-list (cddr expr) 
		     (cons (tag-variable 'catch (cadr expr)) vars)
		     fns)))

(defun require-handler (expr vars fns)
  (notify 'note "Changing *require form, eliminating environment argument ~A"
	  (cadddr expr))
  `(require ,(cadr expr) ,(caddr expr)))

(defun *value-handler (expr vars fns)
  (advise expr (cadr (caddr expr))))

(defun comment-handler (expr vars fns)
  `(comment ,@(cdr expr)))

(defun eval-handler (expr vars fns)
  (notify 'note "Changing EVAL form, eliminating environment argument ~A."
	  (caddr expr))
  (advise expr `(eval ,(cadr expr))))

(defun herald-handler (expr vars fns)
  `(comment ,@(cdr expr)))

(defun variables-bound (specs) 
  (labels ((flatten (x) (cond ((null x) nil)
			      ((atom x) (list x))
			      (t (union (flatten (car x)) 
					(flatten (cdr x)))))))
    (flatten specs)))

(defun convert-operation-specs (specs vars fns)
  (mapcar 
   #'(lambda (x) 
       `(,(car x) 
	 ,@(convert-list (cdr x) (union (variables-bound (cdar x)) vars) fns)))
   specs))


(defun deftype-handler (expr vars fns)

  (let ((fields-handlers (cdr expr))
	(fields nil) 
	(handlers nil))
    (if (listp (car (last fields-handlers)))
	(progn
	  (setq fields (butlast fields-handlers))
	  (setq handlers (car (last fields-handlers))))
      (setq fields fields-handlers))
    (let ((operations-specs (convert-operation-specs handlers vars fns)))
      `(,(car expr) ,@fields ,@(if operations-specs
				   (list operations-specs)
				 nil)))))


(defun object-handler (expr vars fns)
  `(,(car expr)
    ,(convert (cadr expr) vars fns) 
    ,@(convert-operation-specs (cddr expr) vars fns)))

(defun define-handler (expr vars fns)
  
  (if (listp (cadr expr)) 
	     ;;(define (fuba a b c) . body)
      `(,(car expr) 
	,(cadr expr)
	,@(convert-list 
	   (cddr expr)
	   (append vars (variables-bound (cdadr expr)))
	   fns))
    `(,(car expr) ,(cadr expr) ,@(convert-list (cddr expr) vars fns))))

(defun  *define-handler (expr vars fns)
  (notify 'note "*DEFINE being converted to DEFINE, eliminating environment argument.")
  (advise expr (define-handler `(define ,(cadr (caddr expr)) ,@(cdddr expr)) vars fns)))

(defun lset-handler (expr vars fns)
  (advise expr (define-handler `(define ,@(cdr expr)) vars fns)))

(defun lambda-handler (expr vars fns)
  `(,(car expr) 
    ,(cadr expr) 
    ,@(convert-list (cddr expr) 
		   (union vars (variables-bound (cadr expr)))
		   fns)))

(defun receive-handler (expr vars fns)
  `(receive
    ,(cadr expr) 
    ,@(convert-list (cddr expr) 
		    (union vars (variables-bound (cadr expr)))
		    fns)))

(defun mung-var-speclist (spec vars fns)
  (mapcar #'(lambda (x) `(,(car x) ,(convert (cadr x) vars fns))) spec))

(defun mung-fn-speclist (spec vars fns)
  (mapcar #'(lambda (x) `(,(car x)  ,@(convert-list (cdr x) vars fns))) spec))

(defun mung-labels-speclist (spec vars fns)
  (let ((defd-fns (mapcar #'(lambda (x) (tag-variable 'is-labeled (caar x)))
			  spec)))
    (mung-fn-speclist spec vars (append fns defd-fns))))

(defun build-enclosure (outer inner lets flets post-bind-forms body)
  (cond ((and lets flets)
	 `(,outer ,lets (,inner ,flets ,@post-bind-forms ,@body)))
	(lets
	 `(,outer ,lets  ,@post-bind-forms ,@body))
	(flets `(,inner ,flets  ,@post-bind-forms ,@body))
	(t `(block  ,@post-bind-forms ,@body))))

(defun tagged-p (tag val) (and (consp val) (eq (car val) tag)))

(defun variable-tagged (val) (if (consp val) (cdr val) val))

(defun labels-handler (expr vars fns)
  (let ((returned-value
	 (catch 'redo
	   (multiple-value-bind (lets flets post-bind-forms)
	       (filter-speclist '() '() '() (cadr expr))
	     (let ((new-vars (union vars (variables-bound (mapcar #'car lets))))
		   (new-fns (union fns (variables-bound (mapcar #'caar flets)))))
	       (let ((lets (mung-var-speclist lets new-vars fns))
		     (flets (mung-labels-speclist flets new-vars new-fns)))
		 (if (and lets flets)
		     (notify 'warning 

"LABELS clause being broken up into a let and labels. Check that
locale for LET does not contain lexically apparent references to
variables in LABELS. ~% LET: ~A~% LABELS: ~A" lets flets))

		 (advise expr
			 (build-enclosure 'let 'labels lets flets post-bind-forms (convert-list (cddr expr) new-vars new-fns)))))))))
    (if (tagged-p 'is-reset returned-value)
	(progn (notify 'warning "Redoing LABELS")
	       ;;(tag-variable 'is-reset (cdr returned-value))
	       (labels-handler expr 
			       vars 
			       (cons returned-value fns)))
      returned-value)))


(defun let-handler (expr vars fns)
  (let ((returned-value
	 (catch 'redo
	   (multiple-value-bind (lets flets post-bind-forms)
	       (filter-speclist '() '() '() (cadr expr))
	     (let ((new-vars (union vars (variables-bound (mapcar #'car lets))))
		   (new-fns (union fns (variables-bound (mapcar #'caar flets)))))
	       (let ((lets (mung-var-speclist lets new-vars fns))

;;;This would have been better to handle differently: VARS instead of NEW-VARS.
;;;There is no semantic difference, however.

		     (flets (mung-fn-speclist flets new-vars new-fns)))
		 (if (and lets flets)
		     (notify 'warning 

"LET clause being broken up into a LET and LABELS. Check that locale
for LABELS does not contain lexically apparent references to variables
in LET and vice-versa. ~% LET: ~A~% LABELS: ~A" lets flets))

		 (advise expr
			 (build-enclosure 'let 'labels  lets flets post-bind-forms (convert-list (cddr expr) new-vars new-fns)))))))))
    (if (tagged-p 'is-reset returned-value)
	(progn (notify 'warning "Redoing LET")
	       (let-handler expr 
			    vars
			    (cons returned-value fns)))
      returned-value)))

(defun do-handler (expr vars fns)
  (let ((new-vars (union vars (variables-bound (mapcar #'car (cadr expr))))))
    `(,(car expr) ,(mapcar #'(lambda (x) `(,(car x) 
					    ,(convert (cadr x) vars fns)
					    ,@(convert-list (cddr x) new-vars fns)))
			    (cadr expr))
      ,(convert-list (caddr expr) new-vars fns)
      ,@(convert-list (cdddr expr) new-vars fns))))

(defun iterate-handler (expr vars fns)
  (let ((new-vars (union vars (variables-bound (mapcar #'car (caddr expr)))))
	(new-fns (adjoin (tag-variable 'is-labeled (cadr expr)) fns)))
    `(iterate ,(cadr expr)
	    ,(mung-var-speclist (caddr expr) vars fns)
	    ,@(convert-list (cdddr expr) new-vars new-fns))))

;;(mapcar #'(lambda (x) `(,(car x) ,(convert (cadr x) vars fns))) 

(defun let*-handler-strict (expr vars fns)
  (let ((form (car expr))
	(body (cddr expr)))
    (labels ((let*-handler-aux (binders-so-far binders-left vars)
	     (if (null binders-left)
		 `(,form ,binders-so-far ,@(convert-list body vars fns))
	       (let*-handler-aux (append  binders-so-far 
					      (mung-var-speclist (list (car binders-left)) vars fns))
				 (cdr binders-left)
				 (union vars (variables-bound (caar binders-left)))))))
      (let*-handler-aux '() (cadr expr) vars))))

(defun bind-handler (expr vars fns)
  (let ((newvars 
	 (union vars 
		(variables-bound (mapcar #'(lambda (x) (if (symbolp (car x)) (car x)  '()))
					 (cadr expr))))))
    `(,(car expr) 
      ,(mung-var-speclist (cadr expr) vars fns)  
      ,@(convert-list (cddr expr) newvars fns))))
  
(defun destructure-handler (expr vars fns)
  (let ((newvars (union vars (variables-bound (mapcar #'car (cadr expr))))))
    `(,(car expr) ,(cadr expr) ,@(convert-list (cddr expr) newvars fns))))

(defun let*-handler (expr vars fns)
  (let-handler (expand-star-macro (cadr expr) (cddr expr) 'let) vars fns))
		 
(defun cons-at-end (l val)
  (append l (list val)))

(defun lambda-vars (lambda-expr)
  (cadr lambda-expr))

(defun lambda-body (lambda-expr)
  (cddr lambda-expr))

;;((op . args) . body)

(defun handler-body (handler)
  (cdr handler))

(defun handler-args (handler)
  (cdar handler))

(defun handler-op (handler)
  (caar handler))

(defun closure-spec-form (obj) (cadr obj))
(defun handler-spec-forms (obj) (cddr obj))

(defun filter-speclist (lets flets post-bind-forms specs)
  (if (null specs) (values lets flets post-bind-forms)
    (let ((next (car specs)))
      (cond ((listp (car next))
	     (filter-speclist lets 
			      (cons-at-end flets next)
			      post-bind-forms
			      (cdr specs)))
	    ((is-form-p 'lambda (cadr next))
	     (filter-speclist
	      lets
	      (cons-at-end flets
			   `((,(car next)  ,@(lambda-vars (cadr next))) 
			     ,@(lambda-body (cadr next))))
	      post-bind-forms
	      (cdr specs)))
	    ((is-form-p 'object (cadr next))

	     (filter-speclist-object 
	      'make-object
	      'refurnish-object
	      next
	      lets
	      flets
	      post-bind-forms
	      specs))
	    
	    ((is-form-p 'operation (cadr next))
		     
	     (filter-speclist-object 
	      'make-operation-init
	      'refurnish-operation
	      next
	      lets
	      flets
	      post-bind-forms
	      specs))

	    ((symbolp (car next)) 
	     (filter-speclist (cons-at-end lets next) flets  post-bind-forms (cdr specs)))))))

(defvar *counter* 0)

(defun gentemp (str)
  (incf *counter*)
  (intern (format nil "~A~A" str *counter*))
  )


(defun filter-speclist-object 
  (constructor
   refurnisher
   next
   lets
   flets
   post-bind-forms
   specs)
  (notify 'warning "Labels contains object or operation ~A~%" (cadr next))
  (let* ((object-var (car next))
	 (handlers (handler-spec-forms (cadr next)))
	 (function-vars (mapcar #'(lambda (x) (gentemp "FUN-")) handlers))
		    
	 ;;In this case the object closure is defined by a lambda expression.

	 (closure-fn-var (if (is-form-p 'lambda (closure-spec-form (cadr next)))
			     (gentemp "OBJ-FUN-")
			   '()))
	 (closure-var (if (and  (closure-spec-form (cadr next) )
				(not closure-fn-var))
			  (gentemp "PROC-")
			'())))

    (filter-speclist
     (append lets `((,object-var (,constructor)))
	     (if closure-var
		 `((,closure-var ,(cadr next)))
	       '()))
     (append flets
	     (mapcar #'(lambda (fn handler) 
			 `((,fn  ,@(handler-args  handler))
			   ,@(handler-body handler)))
		     function-vars 
		     handlers)

	     (if closure-fn-var
		 `(((,closure-fn-var ,@(lambda-vars (closure-spec-form (cadr next))))					      ,@(lambda-body (closure-spec-form (cadr next))))))
	     '())


				    

     (cons-at-end post-bind-forms `(,refurnisher
				     ,object-var 

				     ,(if closure-fn-var closure-fn-var closure-var)

				     ,@(mapcar #'(lambda (x y)
						   (list (handler-op x) y))
					       handlers
					       function-vars)))
     (cdr specs))))

(defun INITIAL-TEA-READER ()
  (set-dispatch-macro-character #\# #\f (function (lambda (stream sub infix)
						    (declare (ignore stream sub infix))
						    '(false))))
  (set-dispatch-macro-character #\# #\t (function (lambda (stream sub infix)
						     (declare (ignore stream sub infix))
						     '(true))))

  )
(initial-tea-reader)

(defvar *totals* 0)

(defun process-top-level (expr)
;;  (format 't "~%Processing ~A:" (cadr expr))
  (let ((old (progn (setq *counter* 0)
		    (setf (symbol-function 'let-handler) #'old-let-handler)
		    (convert expr nil nil)))
	(new (progn (setq *counter* 0)
		    (setf (symbol-function 'let-handler) #'new-let-handler)
		    (convert expr nil nil))))
    (or (equalp old new)
	(progn (format 't "~%(~A ~A~%" (car expr) (cadr expr))
	       (incf *totals*)))))

(defun old-let-handler (expr vars fns)
  (let ((returned-value
	 (catch 'redo
	   (multiple-value-bind (lets flets post-bind-forms)
	       (filter-speclist '() '() '() (cadr expr))
	     (let ((new-vars (union vars (variables-bound (mapcar #'car lets))))
		   (new-fns (union fns (variables-bound (mapcar #'caar flets)))))
	       (let ((lets (mung-var-speclist lets new-vars fns))

;;;This would have been better to handle differently: VARS instead of NEW-VARS.
;;;There is no semantic difference, however.

		     (flets (mung-fn-speclist flets new-vars new-fns)))
		 (if (and lets flets)
		     (notify 'warning 

"LET clause being broken up into a LET and LABELS. Check that locale
for LABELS does not contain lexically apparent references to variables
in LET and vice-versa. ~% LET: ~A~% LABELS: ~A" lets flets))

		 (advise expr
			 (build-enclosure 'let 'labels  lets flets post-bind-forms (convert-list (cddr expr) new-vars new-fns)))))))))
    (if (tagged-p 'is-reset returned-value)
	(progn (notify 'warning "Redoing LET")
	       (let-handler expr 
			    vars
			    (cons returned-value fns)))
      returned-value)))

(defun new-let-handler (expr vars fns)
  (let ((returned-value
	 (catch 'redo
	   (multiple-value-bind (lets flets post-bind-forms)
	       (filter-speclist '() '() '() (cadr expr))
	     (let ((new-vars (union vars (variables-bound (mapcar #'car lets))))
		   (new-fns (union fns (variables-bound (mapcar #'caar flets)))))
	       (let ((lets (mung-var-speclist lets vars fns))

;;;This would have been better to handle differently: VARS instead of NEW-VARS.
;;;There is no semantic difference, however.

		     (flets (mung-fn-speclist flets new-vars new-fns)))
		 (if (and lets flets)
		     (notify 'warning 

"LET clause being broken up into a LET and LABELS. Check that locale
for LABELS does not contain lexically apparent references to variables
in LET and vice-versa. ~% LET: ~A~% LABELS: ~A" lets flets))

		 (advise expr
			 (build-enclosure 'let 'labels  lets flets post-bind-forms (convert-list (cddr expr) new-vars new-fns)))))))))
    (if (tagged-p 'is-reset returned-value)
	(progn (notify 'warning "Redoing LET")
	       (let-handler expr 
			    vars
			    (cons returned-value fns)))
      returned-value)))

(defun process-source-file (source-dir file suffix)
  (setf *print-case* :downcase)
  (format 't "PROCESSING FILE ~A~%" file)
  (with-open-file 
   (current-in (truename (format nil "~A/~A.~A" source-dir file suffix)) :direction :input)
   (loop
     (let ((sexp (read current-in nil 'eof-value)))
       (if (eql sexp 'eof-value)
	   (progn (close current-in)
		  (return-from process-source-file))
	 (process-top-level sexp))))))

(defun process-source-files (source-dir the-files suffix)
    (mapc #'(lambda (x) (process-source-file 
			 source-dir 
			 (string-downcase (format nil "~A" x))
			 suffix))
	  the-files)
    (format t "~%~%Totals: ~A" *totals*)
    'processing-done)

(defvar *imps-files*
      '(
	"user/def-forms" 
	"user/other-forms"
	"user/imps"
	"user/check-imps"
;;	"user/init"
	"resources/numerical-objects"
	"resources/bitop-numerical-objects"
	"resources/emacs-buffers"
	"resources/lisp-supplements"
	"resources/sets"
	"expressions/sortings"
	"expressions/expressions"
	"expressions/constructors"
	"expressions/quasi-constructors"
	"expressions/innards-for-constructors"
	"expressions/innards-for-languages"
	"expressions/languages"
	"substitution/substitutions"
	"substitution/substitution-application"
	"substitution/alpha-equivalence"
	"substitution/naive-matching"
	"substitution/sort-substitutions"
	"substitution/variable-sorts-matching"
	"expressions/some-constructors"
	"expressions/some-quasi-constructors"
	"expressions/gently"
	"expressions/quasi-sorts"
	"expressions/schemata-for-quasi-constructors"
	"expressions/virtual-paths"
	"presentation/read-print"
	"theory-mechanism/domain-range"
	"theory-mechanism/definitions"
	"theory-mechanism/recursive-definitions"
	"theory-mechanism/sort-definitions"
	"theory-mechanism/mc-extensions"
	"theory-mechanism/sort-constructors"
	"theory-mechanism/history"
	"theory-mechanism/theorem"
	"theory-mechanism/restricted-substitution-definedness"
	"theory-mechanism/transforms"
	"theory-mechanism/theory-transform-interface"
	"theory-mechanism/rewrite-rules"
	"theory-mechanism/transportable-rewrite-rules"
	"theory-mechanism/elementary-macetes"
	"theory-mechanism/transportable-macetes"
	"theory-mechanism/theory-subsorting"
	"theory-mechanism/theory"
	"theory-mechanism/theory-ensembles"
	"theory-mechanism/record-theories"
	"theory-mechanism/sections"
	"inferences/q-classes"
	"inferences/context-sequent"
	"inferences/context-entailment"
	"inferences/syllogistic-inference"
	"inferences/backchain"
	"inferences/rules"
	"inferences/deduction-graphs"
	"inferences/constructor-inferences"
	"inferences/special-rules"
	"inferences/domain-range-inference"
	"inferences/domain-range-rules"
	"inferences/commands"
	"inferences/dg-primitive-inferences"
	"inferences/dg-inferences-interface"
	"inferences/relative-position"
	"inferences/scripts"
	"inferences/informal-justification"
	"presentation/dg-emacs"
	"presentation/theory-emacs"
	"presentation/read-interface"
	"presentation/parse"
	"presentation/presentation-interface"
	"presentation/print"
	"presentation/tex-print-methods"
	"presentation/xtv-interface"
	"presentation/tex-prescriptive-presentation"
	"presentation/sexp-print"
	"presentation/sexp-syntax"
	"presentation/overloading"
	"presentation/macete-help"
	"theory-inference/algebraic"
	"theory-inference/expand"
	"theory-inference/reductions"
	"theory-inference/order"
	"theory-inference/feasible"
	"theory-inference/context-inequalities"
	"theory-inference/equality"
	"theory-inference/macetes"
	"theory-inference/macete-constructors"
	"theory-mechanism/the-kernel-theory"
	"theory-inference/general-macetes"
	"theory-inference/instantiation-strategies"
	"theory-inference/existential-matching"
	"theory-inference/general-strategies"
	"theory-inference/unfolding-strategies"
	"theory-inference/induction-strategies"
	"theory-inference/strategy-combining-forms"
	"theory-mechanism/bnf"
	"translations/translations"
	"translations/obligations"
	"translations/translation-builders"
	"translations/transportations"
	"translations/translation-match"
	"translations/language-transportation"
	"translations/theory-transportation"
	"presentation/imps-commands"
	"presentation/imps-special-commands"
	"presentation/indicator-parse-print"
	"presentation/sequence-parse-print"
	"presentation/command-display"
	"presentation/imps-schemeweb"
	

      ))


      