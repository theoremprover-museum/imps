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

(defun wrap (thing methods)
  (let ((obj (make-object)))
     (setf (object-handlers obj)
	   (apply #'vector
		 (mapcar #'(lambda (op)
			     (vector op
				   #'(lambda (blah &rest args)
				       (declare (ignore blah))
				       (apply (operation-default op) thing args))))
			 methods)))
     obj))

(defvar output-port-methods
  (list tea::close tea::write tea::write-char tea::write-line tea::format tea::force-output tea::output-port? tea::port? tea::newline tea::fresh-line tea::port-name))

(defvar input-port-methods 
  (list tea::port-read-table tea::close tea::read tea::read-line tea::read-char tea::unread-char tea::peek-char tea::input-port? tea::port? tea::port-name))

(defun build-input-port (stream)
  (let ((read-table (copy-readtable *readtable*))
	(last-read-char '())
	(the-setter (setter tea::port-read-table)))
    (declare (special tea::port-read-table tea::read))
    (join (make-object 
	   :handlers (vector 
		      (vector tea::read
			    #'(lambda (soi &rest args)
				(declare (ignore soi))
				(let ((*readtable* read-table))
				  (tea::read stream args))))
		      
		      (vector tea::unread-char
			    #'(lambda (soi)
				(declare (ignore soi))
				(if (characterp last-read-char)
				    (unread-char last-read-char stream))
				(setf last-read-char '())))

		      (vector tea::read-char
			    #'(lambda (soi)
				(declare (ignore soi))
				(let ((ch (read-char stream  nil eof-value nil)))
				  (if (characterp ch)
				      (setf last-read-char ch)
				    (setf last-read-char '()))
				  ch)))

		      (vector the-setter
			    #'(lambda (soi rt)
				(declare (ignore soi))
				(setf read-table rt)))
		      (vector tea::port-read-table
			    #'(lambda (blah)
				(declare (ignore blah))
				read-table))))
	  (wrap stream input-port-methods))))

;;hpos does nothing.

(defun build-output-port (stream)
  (let ((the-pos 0)
	(the-setter (setter tea::hpos)))
    (flet ((output-hpos ()
			(do ((i 0 (+ 1 i))) ((<= i the-pos) 't) (format stream " "))))
      (join (make-object 
	     :handlers (vector 
			(vector the-setter
			      #'(lambda (soi pos)
				  (declare (ignore soi))
				  (setf the-pos pos)))
			(vector tea::hpos
			      #'(lambda (soi)
				  (declare (ignore soi))
				  the-pos))))	     
	    (wrap stream output-port-methods)))))

(defun build-io-port (stream)
  (join (build-input-port stream)
	(build-output-port stream)))


;;;Streams:

;;tea::with-input-from-string etc.. Imported

(defun tea::string->input-port (str)
  (build-input-port (make-string-input-stream str)))
(setf-value-from-function 'tea::string->input-port)

(setf-value-and-closure
 (let ((stdin (build-input-port (make-synonym-stream '*standard-input*))))
   (build-operation 'tea::standard-input
		    #'(lambda () stdin)
		    (vector
		     (vector setter
			   #'(lambda (val) 
			       (declare (ignore val))
			       #'(lambda (v) 
				   (or (tea::input-port? v)
				       (error "~A is not an valid input port for standard input."v))
				   (setf stdin v))))))))

(defmacro tea::with-output-to-string (var . body)
  (let ((stream-var 'output-to-string-var))
    `(let* ((,stream-var (make-string-output-stream))
	    (,var (build-output-port ,stream-var)))
       (unwind-protect
	   (progn ,@body
		  (get-output-stream-string ,stream-var))
	 (tea::close ,var)))))

(defmacro tea::with-input-from-string ((var string) . body)
  `(let ((,var (tea::string->input-port ,string)))
     (unwind-protect
	 (progn ,@body)
       (tea::close ,var))))


(setf-value-and-closure
 (let ((stdout (build-output-port (make-synonym-stream '*standard-output*))))
   (build-operation 'tea::standard-output
		    #'(lambda () stdout)
		    (vector
		     (vector setter
			     #'(lambda (val) 
				 (declare (ignore val))
				 #'(lambda (v) 
				     (or (tea::output-port? v)
					 (error "~A is not an valid output port for standard output."v))
				     (setf stdout v))))))))


(setf-value-and-closure
 (let ((stdout (build-output-port (make-synonym-stream '*error-output*))))
   (build-operation 'tea::error-output
		    #'(lambda () stdout)
		    (vector
		     (vector setter
			     #'(lambda (val) 
				 (declare (ignore val))
				 #'(lambda (v) 
				     (or (tea::output-port? v)
					 (error "~A is not an valid output port for standard output."v))
				     (setf stdout v))))))))



(defun tea::read-objects-from-string (str)
  (let ((accum '()) (offset 0))
    (loop
     (multiple-value-bind (next new-offset)
	 (read-from-string str nil 'eof-sym :start offset)
       (if (eql next 'eof-sym)
	   (return-from tea::read-objects-from-string (nreverse accum))
	 (progn (setq offset new-offset)
		(push next accum)))))))

(setf-value-from-function 'tea::read-objects-from-string)

