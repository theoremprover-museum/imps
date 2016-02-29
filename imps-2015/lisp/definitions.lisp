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

;; The following procedure (with some minor changes) is due to: Sandra
;; Loosemore from the MUMBLE package. Returns a LIST (destructured
;; declaration)

(defun destructure-args (lambda-list)
  (let ((destructured 
	 (cond ((consp lambda-list)
		(let ((last  (last lambda-list)))
		  (if (null (cdr last))
		      lambda-list
		    `(,@(ldiff lambda-list last) ,(car last) &rest ,(cdr last)))))
	       ((null lambda-list)
		'())
	       (t
		`(&rest ,lambda-list)))))
    (let ((ignored nil))
      (setq destructured 
	    (mapcar #'(lambda (x) 
			(if (null x) 
			    (progn
			      (setq x (generate-symbol))
			      (push x ignored)
			      x)
			  x))
		    destructured))
      (if ignored
	  `(,destructured (declare (ignore ,@ignored)))
	`(,destructured)))))

(defmacro tea::define (form . body) 
  (if (listp form)
      (let ((name (car form))
	    (varlist (cdr form)))
	`(progn
	   (defun ,name ,@(destructure-args varlist) ,@body)
	   (proclaim '(special ,name))
	   (setf (symbol-value ',name) (symbol-function ',name))))
    (if (symbolp form)
	`(progn
	   ;;If body is a lambda it will be destructured.
	   (proclaim '(special ,form))
	   (setf (symbol-value ',form) ,@body)
	   
	   (if (is-callable-thing ,form)
	       (setf (symbol-function ',form) (closure ,form)))
	   ;(if (object? ,form) 
;	       (def-object-setf ,form (&rest args) ,(generate-symbol)))
	   ,form)
      (error "Bad syntax ~A ~A" form  body))))

;(defmacro tea::define-variable (var value)
;  `(defvar ,var ,value))
;
;(defmacro tea::define-function ((name . varlist) . body) 
;  `(defun ,name ,@(destructure-args varlist) ,@body))

(defmacro tea::define-syntax (form . body) ;;((name . varlist) . body)
  (let ((name (car form))
	(varlist (cdr form)))
  `(defmacro ,name ,@(destructure-args varlist) ,@body)))

(defmacro tea::define-constant (var value)
  `(tea::define ,var ,value))

(defmacro tea::define-integrable (form . body)
  (if (listp form)
      (let ((name (car form))
	    (varlist (cdr form)))
	`(progn ;;eval-when (eval compile load)
;;	   (proclaim '(inline ,name))
	   (defun ,name ,@(destructure-args varlist) ,@body)
	   (setf (symbol-value ',name) (symbol-function ',name))))
    (if (symbolp form)
      `(progn
	 ;;If body is a lambda it will be destructured.
	 (setf (symbol-value ',form) ,@body)
	 (if (is-callable-thing ,form)
	     (setf (symbol-function ',form) (closure ,form)))
	 ,form)
      (error "Bad syntax ~A ~A" form  body))	))

(defmacro tea::set (gvar value)
  (if (setf-method-p gvar)
      `(setf ,gvar ,value)
    `(tea::funcall (tea::setter ,(car gvar)) ,@(cdr gvar) ,value)))

(defmacro tea::lset (symbol value)
  `(setq ,symbol ,value))

