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

(defvar *default-structure-print*
  #'(lambda (struct stream) (format stream "#<~A ~A>" (type-of struct) (object-id struct))))

;; There are three kinds of callable objects:
;; PROCEDURES and OBJECTS, of which OPERATIONS are special cases.
;; In most cases a variable whose value is one of these will have a value euql to the 
;; corresponding operation:

(defstruct (object (:print-function (lambda (struct stream depth)
				      (funcall *default-structure-print* struct stream)))
		   (:predicate object?))
  id
  closure
  handlers
  )

(defstruct (operation (:include object)
		      (:predicate operation?)
		      (:print-function (lambda (struct stream depth)
					 (funcall *default-structure-print* struct stream)))) 
  default)

(defstruct (switch (:include operation)
		   (:predicate switch?)
		   (:print-function (lambda (struct stream depth) 
				      (funcall *default-structure-print* struct stream))))
  predicate
  state)

(defun closure (the-thing)
  (do ((thing the-thing (object-closure thing)))
      ((not (object? thing)) (the function thing))))

;;A callable thing is always a function, or one way from being one.

(defun setf-value-and-closure (obj)
  (let ((name (object-id obj)))
    (setf (symbol-function name) (object-closure obj))
    (setf (symbol-value name) obj))
  obj)

(defun vcar (vect)  
  (declare (type vector vect))
  (svref vect 0))

(defun dispatch (op object)
  (declare (type operation op) 
	   (type object  object)
	   (ftype (function (object) vector) object-handlers))
  (let ((vect (find op (object-handlers object) :test #'eql :key #'vcar)))
    (if vect (svref vect 1) vect)))


(defun make-operation-init (&rest args)
  (let ((oper (apply #'make-operation args)))
    (setf (operation-closure oper) (operation-applier oper))
    oper))

(defun make-switch-init (&rest args)
  (let ((switch (apply #'make-switch args)))
    (setf (switch-closure switch) (switch-applier switch))
    switch))
  
(defun symbol-operation (symbol)
  (get symbol 'symbol-operation))

(defun set-symbol-operation (symbol value)
  (setf (get symbol 'symbol-operation) value))

(defsetf symbol-operation set-symbol-operation)

(defun operation-applier (oper)
  (function
   (lambda (&rest obj-args) 
     (block apply-operation
       (let ((object (car obj-args))
	     (args (cdr obj-args)))
	 (if (object? object)
	     (let ((hndl (dispatch oper object)))
	       (if hndl (return-from apply-operation (apply hndl object args)))))
	 (let ((def (operation-default oper)))
	   (if def (apply  def obj-args)
	     (error (format nil "OPERATION-APPLIER: Operation ~A has no default method." oper)))))))))

(defun switch-applier (oper)
  (function
   (lambda () (switch-state oper))))

(defun switch-setter (switch)
  (function
   (lambda (val)
     (if (funcall (closure (switch-predicate switch)) val)
	 (setf (switch-state switch) val)
       (error "SWITCH-SETTER: Invalid value ~A for switch ~A" val switch)))))

(defun build-operation (name default handlers)
  (or (symbolp name) (error "BUILD-OPERATION: ~A is not a symbol" name))
  (if (null name) (error "BUILD-OPERATION: ~A invalid name" name))
  (let ((op (make-operation-init
	      :id name 
	      :default default 
	      :handlers handlers)))
       op))

(defvar *setter* 
  (setf-value-and-closure
   (build-operation 'setter
		    #'(lambda (&rest args) 
			(or (extractor-setter (car args))
			    (error "SETTER DEFAULT: No setter for first argument (if any) of argument list ~A"
			      args)))
		   nil)))

;;;for settable operationsk calling the operation *setter* on the operation
;;itself returns a procedure.

(defun build-settable-operation (name default)
  (let ((setter-op (make-operation-init)))
     (build-operation name default
       (vector (vector *setter* (function (lambda (soi) setter-op)))))))

(defun build-predicate (name)
  (build-operation name (function (lambda (x) '())) nil))

(defun build-switch (name init-value predicate)
  (let ((switch 
	 (make-switch-init 
	  :id name 
	  :state init-value 
	  :predicate (or predicate (function (lambda (arg) (declare (ignore arg)) 't)))))
	(setter-op (make-operation-init)))
    (setf (operation-closure setter-op) (switch-setter switch))

    (setf (switch-handlers switch)
	  (vector
	   (vector *setter* (function (lambda (soi) (declare (ignore soi)) setter-op)))))
    switch))

;(defmacro def-object-setf (name lambda-list store-value)
;  `(defsetf-1 ,name ,lambda-list (,store-value)
;     (list 'tea::funcall '(setter (symbol-value ',name))
;	       ,@lambda-list ,store-value)))

(defmacro build-dispatch-table (handlers)
  `(vector 
    ,@(mapcar #'(lambda (x) 
		  `(vector ,(caar x) 
			 (tea::lambda ,(cdar x) ,@(cdr x))))
		   handlers)))

(defun tea::join (&rest objects)
  (let ((obj (make-object)))
    (setf (object-closure obj) 
	  (if objects (object-closure (car objects))
	    nil))
    (setf (object-handlers obj) 
	  (combine-handlers (mapcar #'object-handlers objects)))
    obj))

(setf-value-from-function 'tea::join)

(defun combine-handlers (handlers)
  (delete-duplicates 
   (apply #'concatenate 'vector  handlers)
   :test #'eql 
   :key #'vcar
   :from-end t))

;;operation macros:

(defvar *operation-default-value* 
  (make-thingy :print-function #'(lambda (s) (format s "{Operation Undefined Value}"))))

(defmacro tea::define-operation (&rest args)
  (cond ((symbolp (car args))
	 (let ((name (car args))
	       (vars (list '&rest (gensym))))
	   (or (= (length args) 1)
	       (error "Bad syntax ~A:" args))
	   `(progn
	     (setf-value-and-closure 
	     (build-operation ',name
			      (tea::lambda ,vars (error "~A: No default method for operation." ',name))
			      nil)))))

	((symbolp (caar args))
	 (destructure 
	  ((((name . vars) . body) args))
	  `(progn
	    (setf-value-and-closure 
	    (build-operation ',name
			     (tea::lambda ,vars ,@(or body '(*operation-default-value*)))
			     nil))
	  )))

	('t (destructure (((((name . vars) . body) . handlers) args))
			 `(progn
			   (setf-value-and-closure 
			   (build-operation ',name 
					    (tea::lambda ,vars ,@(or body 
									  '(*operation-default-value*)))
					    (build-dispatch-table ,handlers))))
	    ))))

(defmacro tea::define-simple-switch (name predicate init-value)
  (let ((name (if (symbolp name) 
		  name
		(car name))))
  `(progn
     (setf-value-and-closure
      (build-switch ',name ,init-value ,predicate))
     ;(def-object-setf ,name nil ,(gensym))
     )))
  
;;ALmost the same. For compatability.

(defun tea::make-simple-switch (name predicate &optional init-value)
  (build-switch name init-value predicate))

(defmacro tea::define-predicate (name)
  `(progn (setf-value-and-closure (build-predicate ',name))))

(defmacro tea::define-settable-operation ((name . vars) . body)
  `(progn
     (setf-value-and-closure
      (build-settable-operation ',name 
			       (tea::lambda ,vars ,@(or body '(*operation-default-value*)))))
     ;(def-object-setf ,name ,vars ,(gensym))
     ))

(defmacro tea::object (proc &rest handlers)
  `(make-object
    :closure ,proc
    :handlers (build-dispatch-table ,handlers)))

(defmacro tea::operation (proc &rest handlers)
  `(make-operation-init
    :default ,proc
    :handlers (build-dispatch-table ,handlers)))

(defmacro tea::funcall (fn &rest args)
  `(funcall (closure ,fn) ,@args))

(defmacro tea::apply (fn &rest args)
  `(apply (closure ,fn) ,@args))

(defmacro tea::refurnish-object (object proc &rest handlers)
  `(progn
     (setf (object-closure ,object) ,proc)
     (setf (object-handlers ,object)
	   (vector
	    ,@(mapcar #'(lambda (x) 
			  `(vector ,(car x) ,(cadr x)))
		      handlers)))
     ,object))
	    
(defmacro tea::refurnish-operation (object proc &rest handlers)
  `(progn
     (setf (operation-default ,object) ,proc)
     (setf (operation-handlers ,object)
	   (vector
	    ,@(mapcar #'(lambda (x) 
			  `(vector ,(car x) ,(cadr x)))
		      handlers)))
     ,object))


(setf-value-and-closure
 (build-operation 'tea::identification
		  (function (lambda (thing) 
			      (cond ((object? thing) (object-id thing))
				    ((symbolp thing) (symbol-name thing))
				    ((stringp thing) thing)
				    (t (sxhash thing)))))
		 nil))

(setf-value-and-closure
 (build-operation 'tea::print-type-string 
		  (function (lambda (thing) "Thing"))
		  nil))


;;Lazy evaluation:

(defmacro tea::delay (expr)
  `(make-delayed-object #'(lambda () ,expr)))

(setf-value-and-closure
 (build-operation 'tea::force
		  (function (lambda (thing) thing))
		 nil))

(defun make-delayed-object (thunk)
  (let ((forcedp nil)
	(value nil))
    (make-object :handlers
		 (vector 
		  (vector tea::force
			#'(lambda (soi)
			    (declare (ignore soi))
			    (cond ((not forcedp) 
				   (setf value (funcall thunk))
				   (setf forcedp 't)))
			    value))))))
