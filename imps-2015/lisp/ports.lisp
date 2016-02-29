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

;;We need operation.lisp loaded here:


(setf-value-and-closure
 (build-operation 'tea::port? 
		 (function (lambda (x) (streamp x))) 
		 nil))

(setf-value-and-closure
 (build-operation 'tea::input-port? 
		 (function (lambda (x) (and (streamp x)(input-stream-p x))))
		 nil))

(setf-value-and-closure
 (build-operation 'tea::output-port? 
		 (function (lambda (x) (and (streamp x)(output-stream-p x))) )
		 nil))

(defvar eof-value (make-thingy))
(defvar tea::eof eof-value)
(defvar tea::repl-wont-print (make-thingy))

(defun tea::eof? (val) (eql val eof-value))

(setf-value-and-closure
 (build-operation 'tea::read 
		 (function (lambda (port &optional recursive?)
			     (if (input-stream-p port) 
				 (read port nil eof-value recursive?)
			       (error "~A is not a stream" port))))
		 nil))

(setf-value-and-closure
 (build-operation 'tea::read-char 
		 (function (lambda (port &optional recursive?)
			     (if (input-stream-p port) 
				 (read-char port nil eof-value recursive?)
			       (error "~A is not a stream" port))))
		 nil))

(setf-value-and-closure
 (build-operation 'tea::unread-char 
		 (function (lambda (port char)
			     (if (input-stream-p port) 
				 (unread-char char port)
			       (error "~A is not a stream" port))))
		 nil))
			   

(setf-value-and-closure
 (build-operation 'tea::peek-char 
		 (function (lambda (port &optional recursive?)
			     (if (input-stream-p port) 
				 (peek-char nil port nil eof-value recursive?)
			       (error "~A is not a stream" port))))
		 nil))

(setf-value-and-closure
 (build-operation 'tea::read-line 	
		 (function (lambda (port &optional recursive?)
			     (if (input-stream-p port) 
				 (read-line port nil eof-value recursive?)
			       (error "~A is not a stream" port))))
		 nil))


(setf-value-and-closure
 (build-settable-operation 'tea::port-read-table
			   (function (lambda (port)
				       (if (input-stream-p port)
					   *readtable*
					 (error "~A is not a stream" port))))))
			   
;;OUTPUT

(defun coerce-to-stream (thing)
  (if (eql thing 't)
      *terminal-io*
     (if (null thing)
	 *standard-output*
       thing)))

(setf-value-and-closure
 (build-operation 'tea::write
		 (function (lambda (stream 
				    object 
				    &optional 
				    (escape t)
				    (pretty nil))
			     (setq stream (coerce-to-stream stream))
			     (if (output-stream-p stream) 
				 (write object 
					:stream stream 
					:escape escape
					:pretty pretty)
			       (error "~A is not a stream" stream))))
		 nil))

(setf-value-and-closure
 (build-operation 'tea::display
		 (function (lambda (object port)
			     (if (tea::output-port? port)
				 (tea::write port object nil nil)
			       (error "~A is not a stream" port))))
		 nil))

(setf-value-and-closure
 (build-operation 'tea::write-char
		 (function (lambda (stream object)
			     (setq stream (coerce-to-stream stream))
			     (if (output-stream-p stream) 
				 (write-char object stream)
			       (error "~A is not a stream" stream))))
		 nil))

(setf-value-and-closure
 (build-operation 'tea::newline
		 (function (lambda (stream)
			     (setq stream (coerce-to-stream stream))
			     (if (output-stream-p stream) 
				 (terpri stream)
			       (error "~A is not an output stream" stream))))
		 nil))

(setf-value-and-closure
 (build-operation 'tea::fresh-line
		 (function (lambda (stream)
			     (setq stream (coerce-to-stream stream))
			     (if (output-stream-p stream) 
				 (fresh-line stream)
			       (error "~A is not an output stream" stream))))
		 nil))

(setf (symbol-operation 'tea::writec) (symbol-operation 'tea::write-char))
(setf (symbol-function 'tea::writec) (symbol-function 'tea::write-char))

;;Fixed Tue Oct 28 11:42:23 EST 1997. Added stream argument to error call

(setf-value-and-closure
 (build-operation 'tea::write-line
		 (function (lambda (stream object)
			     (setq stream (coerce-to-stream stream))
			     (if (output-stream-p stream) 
				 (write-line object stream)
			       (error "~A is not a stream" stream))))
		 nil))

(setf-value-and-closure
 (build-operation 'tea::force-output
		 (function (lambda (stream)
			     (setq stream (coerce-to-stream stream))
			     (if (output-stream-p stream) 
				 (force-output stream)
			       (error "~A is not a stream" stream))))
		 nil))

(setf-value-and-closure
 (build-operation 'tea::format
		 (function (lambda (stream control-string &rest args)
			     (if (or (null stream) 
				     (eql stream t)
				     (output-stream-p stream) )
				 (apply #'format stream control-string args)
			       (error "~A is not a valid destination for format" stream))))
		 nil))


(setf-value-and-closure
 (build-operation 'tea::close
		 (function (lambda (stream)
			     (if (streamp stream)
				 (close stream)
			       (error "~A is not a stream" stream))))
		 nil))

(setf-value-and-closure
 (build-settable-operation 'tea::hpos
		 (function (lambda (stream)
			     (if (streamp stream) 0
			       (error "~A is not a stream" stream))))))


(defmacro tea::with-open-ports (specs &rest body)
  `(let ,specs 
     (unwind-protect 
	 (progn ,@body)
       ,@(mapcar #'(lambda (x) `(tea::close ,(car x))) specs))))

(setf-value-and-closure
 (build-operation 'tea::port-name
		 (function (lambda (stream)
			     (or (streamp stream)
				 (error "~A is not a stream" stream))
			     (parse-namestring stream)))
		 nil))

(setf-value-and-closure
 (build-operation 'tea::pretty-print
		  (function (lambda (thing port)
			      (tea::write port thing t t)))
		 nil))

(defvar tea::standard-read-table  *readtable*)
(defvar tea::*vanilla-read-table*
  (let ((table (copy-readtable *readtable*)))
    (do ((i 0 (+ 1 i))) ((< 127 i) table)
      (if (member i '(0 7 8 9 10 12 32) :test #'=)
	  (set-syntax-from-char (code-char i) (code-char 32)
				table *readtable*)
	  (set-syntax-from-char (code-char i) (code-char 97)
				table *readtable*)))))
			    

(defun tea::make-read-table (read-table &optional id)
  (declare (ignore id))
  (copy-readtable read-table))

;;(setf-value-from-function 'tea::make-read-table)

(defun tea::read-table-entry (table char)
  (get-macro-character char table))

(defun macro-char-setter (table char val)
  (if (is-callable-thing  val)
      (set-macro-character char val  nil table)
    nil))

(%defsetf  tea::read-table-entry macro-char-setter)

;;;Printing 

;;Fixed Tue Oct 28 11:42:23 EST 1997. Added  pt argument to error call

(defun print-default (thing pt)
  (or (tea::output-port? pt)
      (error "~A is not an output port" pt))
  (cond ((listp thing)
	 (print-list thing pt))
	((tea::object? thing)
	 (tea::format pt "#<~A ~A>" (type-of thing) (object-id thing)))
	(t
	 (tea::write pt thing))))

(defun print-list (thing pt)
  (if (null thing) (print-null-list pt)
    (progn
      (print-first (car thing) pt)
      (do ((l (cdr thing) (cdr l)))
	  ((atom l) (print-last-atom l pt))
	(tea::format pt " ")
	(tea::print (car l) pt)
	))))

(defun print-null-list (pt)
  (tea::format pt "()"))

(defun print-first (thing pt)
  (tea::format pt "(")
  (tea::print thing pt))

(defun print-last-atom (l pt)
  (if (null l) (tea::format pt ")")
    (progn
      (tea::format pt " . ")
      (tea::print l pt)
      (tea::format pt ")"))))
      
(setf-value-and-closure
 (build-operation 'tea::print
		  (function print-default)
		  
;;;		  (lambda (thing port)
;;;			      (or (tea::output-port? port)
;;;				  (error "~A is not an output port"))
;;;			      (tea::write port thing)))
		 nil))
