(in-package "USER")


(defvar *functions* (make-hash-table))
(defvar *defined* (make-hash-table))
(defvar *lexicals* (make-hash-table))
(defvar *specials* (make-hash-table))
(defvar *top-level-define* nil)

(defun intern-upcase (f-string &rest args)
  (intern (string-upcase (apply #'format nil f-string args))))

(defun nudge (thing table)
;;;  (if (eq table *lexicals*)
;;;      (format t "~%~A" thing))
  (if thing
      (setf (gethash thing table) thing)))

(defun nudge-em (things table)
  (mapc #'(lambda (x) (nudge x table)) things))

;;;(defun table-intersection (table-1 table-2)
;;;  (format 't "~%")
;;;  (maphash #'(lambda (key value) 
;;;	       (if (gethash key table-2)
;;;		   (format 't "~A~%" key)));; (mapcar #'cadr value))))
;;;	   table-1))
;;;
;;;(defun table-difference (table-1 table-2)
;;;  (format 't "~%~%")
;;;  (maphash #'(lambda (key value) 
;;;	       (or (gethash key table-2)
;;;		   (format 't "~A~%" key)))
;;;	   table-1)
;;;  (format 't "~%~%"))

(defun proclaim-specials (filename)
  (with-open-file (port filename :if-does-not-exist :create :if-exists :rename-and-delete :direction :output)
		  (format port "(in-package \"TEA-IMPLEMENTATION\")")
		  (format port "~%~%")
		  (maphash #'(lambda (key value) 
			       (or (gethash key *lexicals*)
				   (format port "(proclaim '(special ~A::~A))~%" (package-name (symbol-package key)) (symbol-name key))))
			   *defined*)
		  (format port "~%~%")))

(defun specials-and-lexicals ()
  (format 't "~%~%")
  (maphash #'(lambda (key value) 
	       (if (gethash key *lexicals*)
		   (format t "~A::~A~%" (package-name (symbol-package key)) (symbol-name key))))
	   *defined*)
  (format 't "~%~%"))

(defun lexicals ()
  (format 't "~%~%")
  (maphash #'(lambda (key value) 
	       (format t "~A::~A~%" (package-name (symbol-package key)) (symbol-name key)))
	   *lexicals*)
  (format 't "~%~%"))

(defun advise (expr_0 expr) expr)

(defun analyze-top-level (expr)
  (analyze expr nil nil))

(defun analyze (expr vars fns)
  (block cond-block
    (cond ((symbolp expr) (or (member expr vars) (nudge expr *specials*)))
	  ((atom expr) )
	  ((let ((handler (dispatch-handler (car expr))))
	     (if handler
		 (return-from cond-block (funcall handler expr vars fns))
	       nil)))
	  (t (or (member (car expr) fns) 
		 (nudge (car expr) *functions*))
	     (analyze-list (cdr  expr) vars fns)))))

(defun analyze-list (l vars fns)
  (mapc #'(lambda (x) (analyze x vars fns)) l))

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
	  (tea::function function-handler)
	  (tea::quote quote-handler)
	  (setf-value-from-function setf-val-handler)
	  (setf-value-and-function setf-val-handler)
	  (setf-value-and-closure  setf-val-closure-handler)
	  (defmacro-synonym dfm-syn-handler)
	  (defvar  quote-handler)
	  (defun  quote-handler)
	  (defstruct  quote-handler)
	  (defsetf   quote-handler)
	  (defmacro  quote-handler)))
	    


(defun is-form-p (form expr)
  (and (listp expr)
       (eq (car expr) form)))

(defun cond-handler (expr vars fns)
  (mapc #'(lambda (x)(analyze-list x vars fns)) (cdr expr)))

(defun select-handler (expr vars fns)
  (analyze (cadr expr) vars fns)
  (mapc #'(lambda (x)
	    (if (atom (car x))
		(analyze (car x) vars fns)
	      (analyze-list (car x) vars fns))
	    (analyze-list (cdr x) vars fns))
	(cddr expr)))

(defun case-handler (expr vars fns)
  (analyze (cadr expr) vars fns)
  (mapc #'(lambda (x)
	    (analyze-list (cdr x) vars fns))
	(cddr expr)))

(defun quote-handler (expr vars fns) expr)

(defun function-handler (expr vars fns) 
  (nudge-em vars *functions*))

(defun variables-lambda-bound (specs) 
  (labels ((flatten (x) (cond ((null x) nil)
			      ((atom x) (list x))
			      (t (union (flatten (car x)) 
					(flatten (cdr x)))))))
    (let ((vars (flatten specs)))
      (nudge-em vars *lexicals*)
      vars)))

(defun variables-dyna-bound (specs) 
  (labels ((flatten (x) (cond ((null x) nil)
			      ((atom x) (list x))
			      (t (union (flatten (car x)) 
					(flatten (cdr x)))))))
    (flatten specs)))


(defun analyze-operation-specs (specs vars fns)
  ;;(((op a b c d) blah) ...)
  (mapc #'(lambda (x) (analyze (caar x) vars fns)) specs)
  (mapc
   #'(lambda (x) 
       (analyze-list (cdr x) (union (variables-lambda-bound (cdar x)) vars) fns))
   specs))


(defun deftype-handler (expr vars fns)
  (let ((*top-level-define*  expr))
    (let ((fields-handlers (cddr expr))
	  (fields nil) 
	  (handlers nil))
      (if (listp (car (last fields-handlers)))
	  (progn
	    (setq fields (butlast fields-handlers))
	    (setq handlers (car (last fields-handlers))))
	(setq fields fields-handlers))
      (nudge (intern-upcase "~A?" (cadr expr)) *defined*)
      (nudge (intern-upcase "make-~A" (cadr expr))  *defined*)
      (nudge-em (mapcar #'(lambda (x) (intern-upcase "~A-~A" (cadr expr) x))
			fields)
		*defined*)
      (analyze-operation-specs handlers vars fns))))

(defun output-to-string-handler (expr vars fns)
  ;;(with-output-to-string-handler p blah)
  (analyze-list (cddr expr) (union vars (variables-lambda-bound (cadr expr))) fns))

(defun object-handler (expr vars fns)
  (analyze (cadr expr) vars fns) 
  (analyze-operation-specs (cddr expr) vars fns))

(defun define-handler (expr vars fns)
  (let ((*top-level-define*  expr))
    (if (listp (cadr expr)) 
	;;(define (fuba a b c) . body)
	(progn
	  (nudge (car (cadr expr)) *defined*)
	  (analyze-list 
	   (cddr expr)
	   (append vars (variables-lambda-bound (cdr (cadr expr))))
	   fns))
      (progn 
	(nudge (cadr expr) *defined*)
	(analyze-list (cddr expr) vars fns)))))

(defun define-syntax-handler (expr vars fns)
    (if (listp (cadr expr)) 
	;;(define (fuba a b c) . body)
	(progn
	  (analyze-list 
	   (cddr expr)
	   (append vars (variables-lambda-bound (cdadr expr)))
	   fns))
      (progn 
	(analyze-list (cddr expr) vars fns))))

(defun set-handler (expr vars fns)
  ;;(set gvar value)
  (if (listp (cadr expr))
      (analyze `(tea::funcall (tea::setter ,(car (cadr expr))) ,@(cdr (cadr expr)) ,(caddr expr)) vars fns)))

(defun lset-handler (expr vars fns)
  (define-handler `(tea::define ,@(cdr expr)) vars fns))

(defun lambda-handler (expr vars fns)
  (analyze-list (cddr expr) 
		(union vars (variables-lambda-bound (cadr expr)))
		fns))

(defun receive-handler (expr vars fns)
  (analyze-list (cddr expr) 
		(union vars (variables-lambda-bound (cadr expr)))
		fns))

(defun analyze-var-speclist (spec vars fns)
  ;;spec is ((v1 vals1)....)
  (variables-lambda-bound (mapcar #'car spec))
  (mapc #'(lambda (x) (analyze (cadr x) vars fns)) spec))

(defun analyze-bind-speclist (spec vars fns)
  ;;spec is ((v1 vals1)....)
  (mapc #'(lambda (x) (set-handler `(tea::set ,(car x) ,(cadr x)) vars fns)) spec))

(defun analyze-fn-speclist (spec vars fns)
  ;;spec is (((f1 a b c) body)....) 
  (mapc #'(lambda (x) 
	    ;;x is ((f1 a b c) body)
	    (let ((new-vars (union vars (variables-lambda-bound (cdar x)))))
	      (analyze-list (cdr x) new-vars fns)))
	spec))

(defun analyze-labels-speclist (spec vars fns)
;;spec is (((fuba a b c) blah1) ... )
  (let ((new-fns (union fns (mapcar #'caar spec))))
    (mapc #'(lambda (x) 
	      ;x is ((fuba a b c) blah1)
	      (let ((new-vars (union vars (variables-lambda-bound (cdar x)))))
		(analyze-list (cdr x) new-vars new-fns)))
	  spec)))

(defun labels-handler (expr vars fns)
;;labels (((fuba a b c) blah1) ... )  body
  (analyze-labels-speclist (cadr expr) vars fns)
  (let ((new (variables-lambda-bound (mapcar #'caar (cadr expr)))))
    (analyze-list (cddr expr) (union vars new) (union fns new))))

(defun let-handler (expr vars fns)
  (analyze-var-speclist (cadr expr) vars fns)
  (let ((new (variables-lambda-bound (mapcar #'car (cadr expr)))))
    (analyze-list (cddr expr) (union vars new) fns)))

(defun flet-handler (expr vars fns)
  (analyze-fn-speclist (cadr expr) vars fns)
  (let ((new (variables-lambda-bound (mapcar #'caar (cadr expr)))))
    (analyze-list (cddr expr) (union vars new) (union vars fns))))

(defun do-handler (expr vars fns)
  (let ((new-vars (union vars (variables-lambda-bound (mapcar #'car (cadr expr))))))
    (mapc #'(lambda (x) (analyze (cadr x) vars fns)
	      (analyze-list (cddr x) new-vars fns))
	  (cadr expr))
    (analyze-list (caddr expr) new-vars fns)
    (analyze-list (cdddr expr) new-vars fns)))

(defun iterate-handler (expr vars fns)
  (let ((new-vars (union vars (variables-lambda-bound (mapcar #'car (caddr expr)))))
	(new-fns (adjoin (cadr expr) fns)))
    (analyze-var-speclist (caddr expr) vars fns)
    (analyze-list (cdddr expr) new-vars new-fns)))

;;(mapcar #'(lambda (x) `(,(car x) ,(analyze (cadr x) vars fns))) 

(defun let*-handler (expr vars fns)
  (if (= (length (cadr expr)) 1)
      (analyze `(tea::let ,@(cdr expr)) vars fns)
    (analyze `(tea::let (,(car (cadr expr))) (tea::let* ,(cdr (cadr expr)) ,@(cddr expr)))
	     vars fns)))

;;;(defun let*-handler (expr vars fns)
;;;  (let ((form (car expr))
;;;	(body (cddr expr)))
;;;    (labels ((let*-handler-aux (binders-left vars)
;;;	     (if (null binders-left)
;;;		 (analyze-list body vars fns)
;;;	       (progn 
;;;		 (analyze-var-speclist (list (car binders-left)) vars fns)
;;;		 (let*-handler-aux 			
;;;		  (cdr binders-left)
;;;		  (union vars (variables-lambda-bound (caar binders-left))))))))
;;;      (let*-handler-aux (cadr expr) vars))))

(defun bind-handler (expr vars fns)
  (let ((newvars 
	 (union vars 
		(variables-dyna-bound (mapcar #'(lambda (x) (if (symbolp (car x)) (car x)  '()))
					 (cadr expr))))))
    (analyze-bind-speclist (cadr expr) vars fns)  
    (analyze-list (cddr expr) newvars fns)))
  
(defun destructure-handler (expr vars fns)
  (analyze-var-speclist (cadr expr) vars fns)
  (let ((newvars (union vars (variables-lambda-bound (mapcar #'car (cadr expr))))))
    (analyze-list (cddr expr) newvars fns)))

(defun dfm-syn-handler (expr vars fns)
  (nudge (cadr expr) *defined*))

(defun setf-val-handler	 (expr vars fns)
   (nudge (cadr (cadr expr)) *defined*))

(defun setf-val-closure-handler  (expr vars fns)
  (if (or (is-form-p 'build-operation (cadr expr))
	  (is-form-p 'build-settable-operation (cadr expr)))
      (nudge (cadr (cadr (cadr expr))) *defined*)
      (nudge (cadr (cadr (caddr (cadr expr)))) *defined*)))

(defun INITIAL-TEA-READER ()
  (set-dispatch-macro-character #\# #\f (function (lambda (stream sub infix)
						    (declare (ignore stream sub infix))
						    '(false))))
  (set-dispatch-macro-character #\# #\t (function (lambda (stream sub infix)
						     (declare (ignore stream sub infix))
						     '(true))))

  )
(initial-tea-reader)

(defvar logport *standard-output*)

(defun analyze-source-file (source-dir file suffix)
  (setf *print-case* :downcase)
  (format 't "PROCESSING FILE ~A~%" file)
  (with-open-file 
   (current-in (truename (format nil "~A/~A.~A" source-dir file suffix)) :direction :input)
   (loop
     (let ((sexp (read current-in nil 'eof-value)))
       (if (eql sexp 'eof-value)
	   (progn (close current-in)
		  (return-from analyze-source-file))
	 (analyze-top-level sexp))))))

(defun analyze-source-files (source-dir the-files suffix package)
  (let ((*package* (find-package  package)))
    (mapc #'(lambda (x) (analyze-source-file 
			 source-dir 
			 (string-downcase (format nil "~A" x))
			 suffix))
	  the-files)
    'analyze-done))

(defvar *imps-files*
      '(
	"user/def-forms" 
	"user/other-forms"
	"user/imps"
	"user/check-imps"
	"user/init"
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


(defvar *implementation-files* 
  '("supplements"
    "ports"
    "wrappers"
    "operations"
    "filesystem"
    "hash"
    ))
      