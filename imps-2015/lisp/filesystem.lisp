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

(defvar *compile-file-type* "o")
(defun tea::chdir (str)
  (setq  *default-pathname-defaults* 
	 (make-pathname :directory (pathname-directory (parse-namestring str))
			:defaults *default-pathname-defaults*)))

(setf-value-and-function 'tea::filename-dir (function pathname-directory))
(setf-value-and-function 'tea::filename-name (function pathname-name))
(setf-value-and-function 'tea::filename-type (function pathname-type))
(setf-value-and-function 'tea::filename->string (function namestring))
(setf-value-and-function 'tea::filename? (function pathnamep))
(setf-value-and-function 'tea::file-exists? (function probe-file))
(setf-value-and-function 'tea::file-delete (function delete-file))

(defun tea::make-pathname (dir name type)
  (make-pathname :directory (pathname-directory (parse-namestring dir))
		 :name name
		 :type type))

;;(defun tea::filename())

(defun symbol-directory (sym)
  (if (tea::symbol-pathname sym)
      (pathname-directory (tea::symbol-pathname sym))
    (append  (pathname-directory *default-pathname-defaults*)
	     (list (string-downcase (symbol-name sym))))))

(defun symbol-type (sym)
  (cond ((null sym) nil)
	((tea::symbol-pathname sym)
	 (or (pathname-type (tea::symbol-pathname sym))
	     (pathname-type *default-pathname-defaults*)))
	(t (pathname-type *default-pathname-defaults*))))

(defun tea::symbol-pathname (sym)
  (get sym 'pathname-default))

(defun set-symbol-pathname (sym val)
  (setf (get sym 'pathname-default) (if (pathnamep val) val
				      (parse-namestring val))))

(%defsetf tea::symbol-pathname set-symbol-pathname)

(defun tea::default-pathname ()
  *default-pathname-defaults* )

(defun default-pathname-setter (val)
  (setf *default-pathname-defaults* (if (pathnamep val) val
				      (parse-namestring val))))

(%defsetf tea::default-pathname default-pathname-setter)


(defun unslashify-symbol (path)
  (tea::read-objects-from-string (substitute #\Space #\/ (symbol-name path))))
	 
(defun symbol-dir-name (path)
  (let ((comps (mapcar #'(lambda (x) (string-downcase (symbol-name x)))
		      (unslashify-symbol path))))
    (values (butlast comps) (car (last comps)))))
	   

(defun tea::->filename (file-spec)
  (cond ((typep file-spec 'pathname) file-spec)
	((stringp file-spec)
	 (merge-pathnames (parse-namestring file-spec)
			  *default-pathname-defaults*))
	((listp file-spec)
	 (multiple-value-bind (dir name)
	     (symbol-dir-name  (cadr file-spec))
	   (let ((dir (append (symbol-directory (car file-spec)) dir))
		 (type (or (if (caddr file-spec)
			       (string-downcase (caddr file-spec))
			     (symbol-type (car file-spec))))))
	     (make-pathname
	      :directory dir
	      :name name
	      :type type
	      :defaults *default-pathname-defaults*))))

	(t (error "Unknown filespec."))))

(setf-value-and-function 'tea::get-default-filename (function tea::->filename))
(setf-value-and-function 'tea::expand-filename (function tea::->filename))
(defun tea::filespec? (x) (declare (ignore x)) 't)
(setf-value-from-function 'tea::filespec?)
  

(defun tea::open (filespec mode-list &optional (if-doesnt-exist :error))
  (let* ((filename (tea::->filename filespec))
	 (direction
	  (cond ((equal mode-list 'tea::in) :input)
		((equal mode-list 'tea::out) :output)
		((equal mode-list 'tea::append) :append)
		((equal mode-list '(tea::in)) :input)
		((equal mode-list '(tea::out)) :output)
		((equal  mode-list '(tea::append)) :append)
		((subsetp '(tea::in tea::out)  mode-list) :io)
		(t (format 't "Mode ~A interpreted as :input" mode-list) :input)))
	 (stream
	  (open filename
		:direction (if (eq direction :append)
			       :output
			     direction)
		:if-exists (if (eq direction :append)
			       :append
			     :supersede)
		:if-does-not-exist (if (or (eq direction :output)
					   (eq direction :append))
				       :create
				     if-doesnt-exist ))))
    (case direction
      ((:input) (build-input-port stream))
      ((:append) (build-output-port stream))
      ((:output) (build-output-port stream))
      ((:io) (build-io-port stream)))))

;;;(defun tea::open (filespec mode-list &optional (if-doesnt-exist :error))
;;;  (let* ((filename (tea::->filename filespec))
;;;	 (direction
;;;	  (cond ((equal mode-list 'tea::in) :input)
;;;		((equal mode-list 'tea::out) :output)
;;;		((equal mode-list 'tea::append) :append)
;;;		((equal mode-list '(tea::in)) :input)
;;;		((equal mode-list '(tea::out)) :output)
;;;		((equal  mode-list '(tea::append)) :append)
;;;		((subsetp '(tea::in tea::out)  mode-list) :io)
;;;		(t (format 't "Mode ~A interpreted as :input" mode-list) :input)))
;;;	 (stream
;;;	  (open filename
;;;		:direction direction 
;;;		:if-does-not-exist (if (eq direction :output)
;;;				       :create
;;;				     if-doesnt-exist ))))
;;;    (case direction
;;;      ((:input) (build-input-port stream))
;;;      ((:append) (build-output-port stream))
;;;      ((:output) (build-output-port stream))
;;;      ((:io) (build-io-port stream)))))

(defun tea::maybe-open (filespec mode-list)
  (tea::open filespec mode-list nil))
	   
(defun tea::require (module file-spec &rest args)
  (declare (ignore args))
  (let* ((pathname (tea::->filename file-spec)))
    (if module (require module pathname)
      (load pathname))))

(defun tea::load (filespec)
  (load (tea::->filename filespec) :verbose nil))
(setf-value-from-function 'tea::load)

(setf-value-and-function 'tea::*require (function tea::require))

(setf-value-and-function 'tea::provide (function provide))

(defun tea::compile-file (filespec)
  (compile-file (tea::->filename filespec)))

(setf-value-from-function 'tea::compile-file)

(defun tea::compile-if-outdated (filespec)
  (let* ((fname (tea::->filename filespec))
	 (new-name (make-pathname :directory (pathname-directory fname)
				  :name (pathname-name fname)
				  :type *compile-file-type*))

	 (date-1 (file-write-date fname))
	 (date-2 (file-write-date new-name)))
    (if (< date-2 date-1)
	(compile-file fname)
      nil)))

(setf-value-from-function 'tea::compile-if-outdated)
