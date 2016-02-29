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

(defmacro tea::define-structure-type (the-name &rest fields-handlers)
  (let ((fields nil) 
	(handlers nil) 
	(raw-constructor-name (concatenate-symbol the-name '-raw-constructor))
	(constructor-name (concatenate-symbol  'make- the-name))
	(copier-name (concatenate-symbol  the-name '-copier ))
	(predicate-name (concatenate-symbol the-name '?))
	(attribute-vector-name (concatenate-symbol the-name '-attributes))
	(handler-vector-name (concatenate-symbol the-name '-handlers))
	(stype-symbol (concatenate-symbol the-name '-stype))
	(n 0))
    (if (listp (car (last fields-handlers)))
	(progn
	  (setq fields (butlast fields-handlers))
	  (setq handlers (car (last fields-handlers))))
      (setq fields fields-handlers))
    (setq n (length fields))
    `(progn
       (defstruct (,the-name
		   (:include object) 
		   (:print-function 
		    (lambda (struct stream depth) 
		      (funcall *default-structure-print* struct stream)))
		   (:predicate ,predicate-name)
		   (:copier ,copier-name)
		   (:constructor ,raw-constructor-name))
	 attributes)
       (setf-value-from-function ',predicate-name)
       ,@(let ((index 0))
	   (mapcar #'(lambda (attribute-name) 
		       (prog1 
			   `(setf-attribute-value-function-and-setter 
			     ,the-name 
			     ,attribute-vector-name 
			     ,attribute-name 
			     ,index)
			 (incf index)))
		   fields))

       ;;Create the master and put on a plist:
       (setf (get ',stype-symbol 'stype-master) (,raw-constructor-name))
       (setf (,attribute-vector-name (get ',stype-symbol 'stype-master))
	     (make-array '(,n)))
       (setf (,handler-vector-name (get ',stype-symbol 'stype-master))
	     (build-dispatch-table ,handlers))

       (defun ,constructor-name ()
	 (let ((new (,copier-name (get ',stype-symbol 'stype-master))))
	   (setf (,attribute-vector-name new) (copy-seq (,attribute-vector-name new)))
	   new))

       (get ',stype-symbol 'stype-master))))

(defvar struct-setter-table (make-hash-table))

(defmacro setf-attribute-value-function-and-setter 
  (struct-name attribute-vector-name attribute-name index)
  (let ((attribute-full-name (concatenate-symbol struct-name '- attribute-name))
	(attribute-setter-name (concatenate-symbol struct-name '- attribute-name '-setter)))
  `(progn
     (defun ,attribute-full-name (struct)
       (svref (,attribute-vector-name struct) ,index))
     (setf-value-from-function ',attribute-full-name)
     (defun ,attribute-setter-name (struct new-value)
       (setf (svref (,attribute-vector-name struct) ,index) new-value))
     (setf (gethash ,attribute-full-name struct-setter-table)
	   (function ,attribute-setter-name)))))

(defun extractor-setter (extractor)
  (gethash extractor struct-setter-table))

;;;(defmacro stype-copier (master copier field-attribute)
;;;  `(function (lambda () (let ((new (,copier ,master)))
;;;			 (setf (,field-attribute new) 
;;;			       (copy-seq (,field-attribute new)))
;;;			 new))))

;;This is a bit of a hack.

(defmacro tea::stype-master (symbol)
  `(get ',symbol 'stype-master))
