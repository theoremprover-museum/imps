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

#+kcl (defvar system-call-proc #'system)

;; Modification by W. M. Farmer Mon Mar 22 2004
;; "'shell" changed to "'user::shell".

#+clisp  (defvar system-call-proc #'user::shell)

#+allegro  (defvar system-call-proc #'excl::run-shell-command)

#+kcl (defmacro tea::gc () `(si::gbc 't))
#+clisp (defmacro tea::gc () `(gc))
#+cmu (defmacro tea::gc () `(gc))
#+allegro (defmacro tea::gc () `(excl::gc))

;;;(setf (tea::symbol-pathname 'tea::reals) 
;;;      (make-pathname :directory 
;;;		    (pathname-directory (parse-namestring "/afs/rcf/project/imps/sys/tea/theories/reals/"))
;;;		    :type "t"))

#-cmu
(defvar *communication-file* (parse-namestring "/tmp/init-comms"))

#-cmu
(defun communication-file () (namestring *communication-file*))

#-cmu
(defun tea::reset-comm-file ()
  (setq  *communication-file* 
	 (parse-namestring (format nil "/tmp/comm-file-~A" (get-universal-time)))))

(defun init-reader (readtable)
  (set-dispatch-macro-character #\# #\f 
				#'(lambda (stream sub infix) 
				    (declare (ignore stream sub infix))
				    '())
				readtable)
  (set-dispatch-macro-character #\# #\t 
				#'(lambda (stream sub infix)
				    (declare (ignore stream sub infix))
				    't)
				readtable))

(defun ool-reset-macro (char)
  (set-macro-character char #'(lambda (stream char)
				(declare (ignore stream char))
				(tea::ool))))

#-cmu 
(defun system-evaluate-string (str)
  (funcall system-call-proc (format nil "~A > ~A" str (communication-file)))
  (unwind-protect
      (with-open-file 
       (commie (communication-file) :direction :input :if-does-not-exist nil)
       (with-output-to-string 
	(out)
	(loop
	 (let ((thing (read-line commie nil 'eof-value)))
	   (if (eq thing 'eof-value)
	       (return)
	     (progn
	       (fresh-line out)
	       (write thing :stream out :escape nil)))))))
    (funcall system-call-proc (format nil "rm -f ~A" (communication-file)))))

#+cmu 
(defun system-evaluate-string (str)
  (with-output-to-string (p) (extensions::run-program "sh" (list "-c" str) :output p)))  

#-cmu
(defun tea::unix-getenv (var)
  (system-evaluate-string (format nil "echo $~A" var)))

#+cmu
(defun tea::unix-getenv (var)
  (system-evaluate-string (format nil "echo -n $~A" var)))

(defvar *user* "jt") ;;(system-evaluate-string "whoami"))

(defun tea::user() *user*)

(defun set-user (user) (setf *user* user))

(%defsetf tea::user set-user)

(init-reader *readtable*)

(proclaim '(special *display-object-to-index-table*))
(proclaim '(special *last-displayed-index*))
(proclaim '(special *display-index-to-object-table*))

(defun tea::print-objects-verbosely ()
  (or *display-object-to-index-table*
      (setq *display-object-to-index-table* (make-hash-table)))
  (or *display-index-to-object-table* 
      (setq *display-index-to-object-table* (make-hash-table)))
  (setf-value-and-function 
   'tea::object-hash
   #'(lambda (x)
       (or (gethash x *display-object-to-index-table*)
	   (progn (incf *last-displayed-index*)
		  (setf (gethash *last-displayed-index* *display-index-to-object-table*) x)
		  (setf (gethash x *display-object-to-index-table*) *last-displayed-index*)
		  *last-displayed-index*))))
  (setq *default-structure-print* 
	#'(lambda (struct stream) (format stream (with-output-to-string (p) (tea::print struct p))))))

(defun tea::print-objects-compactly ()
  (setf-value-and-function 'tea::object-hash #'sxhash)
  (setq *default-structure-print*  
        #'(lambda (struct stream)(format stream "#<~A ~A>" (type-of struct) (object-id struct)))))

(defun tea::print-objects-parsimoniously ()
  (setf-value-and-function 'tea::object-hash #'sxhash)
  (setq *default-structure-print*   
        #'(lambda (struct stream) (declare (ignore struct)) (format stream "#<>"))))