(in-package "TEA-IMPLEMENTATION")


(defvar *expression-free-variables* nil)

(defun intern-upcase (f-string &rest args)
  (intern (string-upcase (apply #'format nil f-string args))))

(defun nudge (thing)
  (if thing
      (push thing *expression-free-variables*)))

(defun nudge-em (things some-list)
  (mapc #'(lambda (x) (nudge x)) things))

(defun advise (expr_0 expr) expr)

(defun free-variables-top-level (expr)
  (let ((*expression-free-variables* nil))
    (free-variables expr nil nil)
    (remove-duplicates *expression-free-variables*)))

(defun free-variables (expr vars fns)
  (block cond-block
    (cond ((symbolp expr) (or (member expr vars) (nudge expr)))
	  ((atom expr) )
	  ((let ((handler (dispatch-handler (car expr))))
	     (if handler
		 (return-from cond-block (funcall handler expr vars fns))
	       nil)))
	  (t (free-variables-list (cdr  expr) vars fns)))))

(defun free-variables-list (l vars fns)
  (mapc #'(lambda (x) (free-variables x vars fns)) l))

(defvar dispatch-handler-alist '())

(defun dispatch-handler (expr)
  (cdr (assoc expr dispatch-handler-alist)))

(defun add-handler (name handler)
  (setq dispatch-handler-alist
	(cons (cons name handler)  dispatch-handler-alist)))

(mapcar #'(lambda (x) (add-handler (car x) (cadr x)))
	'((tea::define  define-handler)
	  (tea::define-operation   define-handler)
	  (tea::define-predicate define-handler)
	  (tea::define-integrable define-handler)
	  (tea::define-settable-operation define-handler)
	  (tea::define-syntax  define-syntax-handler)
	  (tea::define-structure-type deftype-handler)
	  (tea::lambda lambda-handler)
	  (tea::cond cond-handler)
	  (tea::xcond cond-handler)
	  (tea::case case-handler)
	  (tea::xcase case-handler)
	  (tea::labels labels-handler)
	  (tea::let let-handler)
	  (tea::flet flet-handler)
	  (tea::do do-handler)
	  (tea::destructure destructure-handler)
	  (tea::destructure* let*-handler)
	  (tea::bind bind-handler)
	  (tea::receive receive-handler)
	  (tea::with-open-ports let-handler)
	  (tea::with-output-to-string output-to-string-handler)
	  (tea::let* let*-handler)
	  (tea::object object-handler)
	  (tea::set set-handler)
	  (tea::operation object-handler)
	  (tea::iterate iterate-handler)
	  (tea::comment quote-handler)
	  (tea::herald quote-handler)
	  (tea::select select-handler)
	  (tea::refurnish-object  refurnish-object-handler)
	  (tea::function function-handler)
	  (tea::quote quote-handler)))

(defun is-form-p (form expr)
  (and (listp expr)
       (eq (car expr) form)))

(defun cond-handler (expr vars fns)
  (mapc #'(lambda (x)(free-variables-list x vars fns)) (cdr expr)))

(defun select-handler (expr vars fns)
  (free-variables (cadr expr) vars fns)
  (mapc #'(lambda (x)
	    (if (atom (car x))
		(free-variables (car x) vars fns)
	      (free-variables-list (car x) vars fns))
	    (free-variables-list (cdr x) vars fns))
	(cddr expr)))

(defun case-handler (expr vars fns)
  (free-variables (cadr expr) vars fns)
  (mapc #'(lambda (x)
	    (free-variables-list (cdr x) vars fns))
	(cddr expr)))

(defun quote-handler (expr vars fns) expr)

(defun function-handler (expr vars fns) 
  (nudge-em vars))

(defun variables-lambda-bound (specs) 
  (labels ((flatten (x) (cond ((null x) nil)
			      ((atom x) (list x))
			      (t (union (flatten (car x)) 
					(flatten (cdr x)))))))
    (flatten specs)))

(defun variables-dyna-bound (specs) 
  (labels ((flatten (x) (cond ((null x) nil)
			      ((atom x) (list x))
			      (t (union (flatten (car x)) 
					(flatten (cdr x)))))))
    (flatten specs)))


(defun free-variables-operation-specs (specs vars fns)
  ;;(((op a b c d) blah) ...)
  (mapc #'(lambda (x) (free-variables (caar x) vars fns)) specs)
  (mapc
   #'(lambda (x) 
       (free-variables-list (cdr x) (union (variables-lambda-bound (cdar x)) vars) fns))
   specs))


(defun deftype-handler (expr vars fns)
  (let ((fields-handlers (cddr expr))
	(fields nil) 
	(handlers nil))
    (if (listp (car (last fields-handlers)))
	(progn
	  (setq fields (butlast fields-handlers))
	  (setq handlers (car (last fields-handlers))))
      (setq fields fields-handlers))
    (free-variables-operation-specs handlers vars fns)))

(defun output-to-string-handler (expr vars fns)
  ;;(with-output-to-string-handler p blah)
  (free-variables-list (cddr expr) (union vars (variables-lambda-bound (cadr expr))) fns))

(defun object-handler (expr vars fns)
  (free-variables (cadr expr) vars fns) 
  (free-variables-operation-specs (cddr expr) vars fns))

(defun refurnish-object-handler (expr vars fns)
  ;;
  (free-variables (cadr expr) vars fns) 
  (free-variables-refurnish-object-specs (cddr expr) vars fns))

(defun free-variables-refurnish-object-specs (specs vars fns)
  (mapc
   #'(lambda (x) 
       (free-variables-list x vars fns))
   specs))

(defun define-handler (expr vars fns)
  (if (listp (cadr expr)) 
      ;;(define (fuba a b c) . body)
      (free-variables-list 
       (cddr expr)
       (append vars (variables-lambda-bound (cdr (cadr expr))))
       fns)))

(defun define-syntax-handler (expr vars fns)
    (if (listp (cadr expr)) 
	;;(define (fuba a b c) . body)
	(progn
	  (free-variables-list 
	   (cddr expr)
	   (append vars (variables-lambda-bound (cdadr expr)))
	   fns))
      (progn 
	(free-variables-list (cddr expr) vars fns))))

(defun set-handler (expr vars fns)
  ;;(set gvar value)
   (if (setf-method-p (cadr expr))
       (free-variables-list (cdr expr) vars fns)
     (if (listp (cadr expr))
	 (free-variables `(tea::funcall (tea::setter ,(car (cadr expr))) ,@(cdr (cadr expr)) ,(caddr expr)) vars fns))))

(defun lset-handler (expr vars fns)
  (define-handler `(tea::define ,@(cdr expr)) vars fns))

(defun lambda-handler (expr vars fns)
  (free-variables-list (cddr expr) 
		(union vars (variables-lambda-bound (cadr expr)))
		fns))

(defun receive-handler (expr vars fns)
  (free-variables-list (cddr expr) 
		(union vars (variables-lambda-bound (cadr expr)))
		fns))

(defun free-variables-var-speclist (spec vars fns)
  ;;spec is ((v1 vals1)....)
  (variables-lambda-bound (mapcar #'car spec))
  (mapc #'(lambda (x) (free-variables (cadr x) vars fns)) spec))

(defun free-variables-bind-speclist (spec vars fns)
  ;;spec is ((v1 vals1)....)
  (mapc #'(lambda (x) (set-handler `(tea::set ,(car x) ,(cadr x)) vars fns)) spec))

(defun free-variables-fn-speclist (spec vars fns)
  ;;spec is (((f1 a b c) body)....) 
  (mapc #'(lambda (x) 
	    ;;x is ((f1 a b c) body)
	    (let ((new-vars (union vars (variables-lambda-bound (cdar x)))))
	      (free-variables-list (cdr x) new-vars fns)))
	spec))

(defun free-variables-labels-speclist (spec vars fns)
;;spec is (((fuba a b c) blah1) ... )
  (let ((new-fns (union fns (mapcar #'caar spec))))
    (mapc #'(lambda (x) 
	      ;x is ((fuba a b c) blah1)
	      (let ((new-vars (union vars (variables-lambda-bound (cdar x)))))
		(free-variables-list (cdr x) new-vars new-fns)))
	  spec)))

(defun labels-handler (expr vars fns)
;;labels (((fuba a b c) blah1) ... )  body
  (free-variables-labels-speclist (cadr expr) vars fns)
  (let ((new (variables-lambda-bound (mapcar #'caar (cadr expr)))))
    (free-variables-list (cddr expr) (union vars new) (union fns new))))

(defun let-handler (expr vars fns)
  (free-variables-var-speclist (cadr expr) vars fns)
  (let ((new (variables-lambda-bound (mapcar #'car (cadr expr)))))
    (free-variables-list (cddr expr) (union vars new) fns)))

(defun flet-handler (expr vars fns)
  (free-variables-fn-speclist (cadr expr) vars fns)
  (let ((new (variables-lambda-bound (mapcar #'caar (cadr expr)))))
    (free-variables-list (cddr expr) (union vars new) (union vars fns))))

(defun do-handler (expr vars fns)
  (let ((new-vars (union vars (variables-lambda-bound (mapcar #'car (cadr expr))))))
    (mapc #'(lambda (x) (free-variables (cadr x) vars fns)
	      (free-variables-list (cddr x) new-vars fns))
	  (cadr expr))
    (free-variables-list (caddr expr) new-vars fns)
    (free-variables-list (cdddr expr) new-vars fns)))

(defun iterate-handler (expr vars fns)
  (let ((new-vars (union vars (variables-lambda-bound (mapcar #'car (caddr expr)))))
	(new-fns (adjoin (cadr expr) fns)))
    (free-variables-var-speclist (caddr expr) vars fns)
    (free-variables-list (cdddr expr) new-vars new-fns)))

;;(mapcar #'(lambda (x) `(,(car x) ,(free-variables (cadr x) vars fns))) 

(defun let*-handler (expr vars fns)
  (if (= (length (cadr expr)) 1)
      (free-variables `(tea::let ,@(cdr expr)) vars fns)
    (free-variables `(tea::let (,(car (cadr expr))) (tea::let* ,(cdr (cadr expr)) ,@(cddr expr)))
	     vars fns)))

(defun bind-handler (expr vars fns)
  (let ((newvars 
	 (union vars 
		(variables-dyna-bound (mapcar #'(lambda (x) (if (symbolp (car x)) (car x)  '()))
					 (cadr expr))))))
    (free-variables-bind-speclist (cadr expr) vars fns)  
    (free-variables-list (cddr expr) newvars fns)))
  
(defun destructure-handler (expr vars fns)
  (free-variables-var-speclist (cadr expr) vars fns)
  (let ((newvars (union vars (variables-lambda-bound (mapcar #'car (cadr expr))))))
    (free-variables-list (cddr expr) newvars fns)))

(defun wrap-local-declaration (free-vars expr)
  `(locally (declare (special ,@free-vars)) ,expr))