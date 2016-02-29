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

(in-package "TEA")

(defstruct (object (:print-function (function (lambda (struct stream depth)
						(format stream "{object ~A}" (object-id struct)))))
		   (:predicate object?))
  id
  default
  handled-operations
  dispatch
  )

(defstruct (operation (:include object)
		      (:predicate operation?)
		      (:print-function (function (lambda (struct stream depth)
						(format stream "{operation ~A}" (operation-id struct)))))) 
  function)

(defstruct (switch (:include operation)
		   (:predicate switch?)
		   (:print-function (function (lambda (struct stream depth) (format stream "{switch ~A}" (switch-id struct))))))
  predicate
  state)

;;Handlers can be simple alists or hash-tables.

(defun dispatch (op object)
  (cdr (find op (object-handlers object) :test 'equal :key 'car)))

(defmacro dispatch-init (object handlers)
  `(progn
     (setf (object-handled-operations ,object)
	   (mapcar #'car ,handlers))
     (setf (object-dispatch ,object)
	 (function (lambda (oper) 
		     (select oper
			     ,@(build-dispatch-table handlers) (else nil)))))
     ,object))
			     

(defun make-operation-init (&rest args)
  (let ((oper (apply #'make-operation args)))
    (setf (operation-function oper) (operation-applier oper))
    oper))

(defun make-switch-init (&rest args)
  (let ((switch (apply #'make-switch args)))
    (setf (switch-function switch) (switch-applier switch))
    switch))
  
(defun symbol-operation (symbol)
  (get symbol 'symbol-operation))

(defun set-symbol-operation (symbol value)
  (setf (get symbol 'symbol-operation) value))

(defsetf symbol-operation set-symbol-operation)

(defun operation-applier (oper)
  (function
   (lambda (object &rest args)
     (block apply-operation
       (if (object-p object)
	   (let ((hndl (funcall (object-dispatch object) oper)))
	     (if hndl (return-from apply-operation (apply hndl object args)))))
       (let ((def (object-default oper)))
	 (if def (apply  def object args)
	   (error (format nil "~A has no default" oper))))))))

(defun switch-applier (oper)
  (function
   (lambda () (switch-state oper))))

(defun switch-setter (switch)
  (function
   (lambda (val)
     (if (funcall (switch-predicate switch) val)
	 (setf (switch-state switch) val)
       (error "Invalid value ~A for switch ~A" val switch)))))

(defun build-operation (name default handlers)
  (or (symbolp name) (error "~A is not a symbol" name))
  (if (null name) (error "~A invalid name" name))
  (let ((op (make-operation-init
	      :id name 
	      :default default 
	      :handlers handlers)))
       (setf (symbol-function name) (operation-function op))
       (setf (symbol-operation name) op)
       op))

(defvar *operation-setter* (build-operation 'operation-setter nil nil))

(defun build-settable-operation (name default)
  (let ((setter-op (make-operation-init)))
     (build-operation name default
       (list (cons *operation-setter* (function (lambda (soi) setter-op)))))))

(defun build-predicate (name)
  (build-operation name (function (lambda (x) '())) nil))

(defun build-switch (name &optional init-value predicate)
  (let ((switch 
	 (make-switch-init 
	  :id name 
	  :state init-value 
	  :predicate (or predicate (function (lambda (arg) 't)))))
	(setter-op (make-operation-init)))
    (setf (operation-function setter-op) (switch-setter switch))
    (setf (symbol-function name) (operation-function switch))
    (setf (symbol-operation name) switch)
    (setf (switch-handlers switch)
	  (list
	   (cons *operation-setter* (function (lambda (soi) setter-op)))))
    switch))

(defmacro def-operation-setf (name lambda-list store-value)
  `(defsetf ,name ,lambda-list ,store-value
     (list 'funcall '(operation-function (operation-setter (symbol-operation ',name)))
	       ,@lambda-list ,@store-value)))

(defmacro build-dispatch-table(handlers)
  (mapcar #'(lambda (x) 
	      (list (caar x) 
		    `(function (lambda ,(cdar x) ,@(cdr x)))))
	  handlers))

(defun join (&rest objects)
  (let ((obj (make-object)))
    (setf (object-default obj) 
	  (if objects (object-default (car objects))
	    nil))
    (setf (object-handlers obj) 
	  (combine-handlers (mapcar #'object-handlers objects)))
    obj))

(defun combine-handlers (handlers)
  (let ((accum '()))
    (mapc #'(lambda (han) 
	      (map nil #'(lambda (x)
			   (if (assoc (car x) accum) nil
			     (setq accum (cons x accum))))
		    han))
	  handlers)
    (apply #'list accum)))

;;operation macros:

(defmacro define-operation (&rest args)
  (if (symbolp (caar args))
      (destructure 
       ((((name . vars) . body) args))
       `(build-operation ',name
			 (function (lambda ,vars ,@(or body '(()))))
			 nil))
       (destructure (((((name . vars) . body) . handlers) args))
		    `(build-operation ',name 
				      (function (lambda ,vars ,@(if body body 
								  '(()))))
				      (build-dispatch-table ,@handlers)))))

(defmacro define-switch ((name) &optional init-value predicate)
  `(progn 
     (build-switch ',name ,init-value ,predicate)
     (def-operation-setf ,name nil (gensym))))
  
(defmacro define-predicate (name)
  `(build-predicate ',name))

(defmacro define-settable-operation ((name . vars) . body)
  `(progn 
     (build-settable-operation ',name 
			       (function (lambda ,vars ,@(or body '(()))))
			       nil)
     (def-operation-setf ,name ,vars (gensym))))

(build-settable-operation 'carro)

(build-settable-operation 'cdrro)

(build-predicate 'listap)

(def-operation-setf cdrro (soi) (v))

(defun haz-lista (a b)
  (object nil
	  (((operation listap) soi) 't)
	      (((symbol-operation 'carro) soi) a)
	      (((symbol-operation 'cdrro) soi) b)
	      (((operation-setter (symbol-operation 'carro)) soi z) (setq a z))
	      (((operation-setter (symbol-operation 'cdrro)) soi z) (setq b z)))))
l
