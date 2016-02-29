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


(defstruct 
  (safe-table (:predicate tea::hash-table?)
		   (:print-function (lambda (str p d)
				      (declare (ignore d))
				      (format p "{Hash Table ~A}" 
					      (safe-table-id str)))))
  id
  type
  test
  table
  key-on                                ;some function on keys.
  deferred
					; list of key-value pairs which have not yet been added to the
		; table because it is currently being walked
  active-key      ;non-nil if table-walking is currently going on for this table
)

(defun tea::make-hash-table (test id &optional (key-on #'tea::identity))
  (let ((table (make-safe-table
		:test test
		:id id
		:key-on key-on
		:deferred '() 
		:active-key '()))
	(real-table (make-hash-table :test test)))
    (setf (safe-table-table table) real-table)
    table))
(setf-value-from-function 'tea::make-hash-table)
(setf-value-and-function 'tea::table? (function tea::hash-table?))

(defun tea::walk-table (fn table)
  (unwind-protect
      (maphash #'(lambda (key val) 
		   (or (safe-table-active-key table)
		       (setf (safe-table-active-key table) key))
		   (funcall (closure fn) key val)
		   (setf (safe-table-active-key table) '()))		     
	       (safe-table-table table))
    (setf (safe-table-active-key table) '())
    (table-flush-deferred table)
    't))
(setf-value-from-function 'tea::walk-table)

(defun table-flush-deferred (table)
  (mapc #'(lambda (x) 
	    (setf (gethash (car x) (safe-table-table table)) (cdr x)))
	  (delete-duplicates 
	   (safe-table-deferred table)
	   :test (safe-table-test table)
	   :key #'car
	   :from-end t))
  (setf (safe-table-deferred table) nil))
  
(defun tea::table-entry (table key)
  (let ((key (funcall (closure (safe-table-key-on table)) key)))
    (let ((deferred (assoc key 
			   (safe-table-deferred table)
			   :test (safe-table-test table))))
      (if deferred (cdr deferred)
	(gethash key (safe-table-table table))))))

;;remark: this will not work correctly for the key nil.

(defun table-entry-setter (table key value)
   (let ((key (funcall (closure (safe-table-key-on table)) key)))
     (if (or (null  (safe-table-active-key table))
	     (eql key (safe-table-active-key table)))
	 (setf (gethash key (safe-table-table table)) value)
       (setf (safe-table-deferred table)
	     (cons (cons key value)
		   (safe-table-deferred table))))))
      

(%defsetf tea::table-entry table-entry-setter)

(defun tea::make-table (&optional id)
  (tea::make-hash-table #'eql id))
(setf-value-from-function 'tea::make-table)
;;Various other kinds of tables:

;;;SET TABLES:

(defun tea::make-string-table (&optional id)
  (tea::make-hash-table #'equal id))
(setf-value-from-function 'tea::make-string-table)


(defun tea::make-set-table (&optional id)
  (let ((tbl (tea::make-hash-table #'equal id #'sort-list-hashfully)))
    (setf (safe-table-type tbl) 'set-table)
    tbl))

(defun tea::set-table? (table)
  (eql (safe-table-type table) 'set-table))

(setf-value-from-function 'tea::set-table?)

(defun tea::table->set (the-table)
  (let ((the-set nil))
    (maphash #'(lambda (key value)
		 (declare (ignore key))
		 (setq the-set (adjoin value the-set)))
	     (safe-table-table the-table))
    the-set))

;;TWO-D TABLES:

(defun tea::two-d-table-entry (table key1 key2)
  (let ((subtable (tea::table-entry table key1)))
    (and subtable
	 (tea::table-entry subtable key2))))

(defun tea::two-d-table-entry-setter (table key1 key2 new-value)
  (let ((subtable (tea::table-entry table key1)))
    (if subtable
	(setf (tea::table-entry subtable key2) new-value)
      (progn
	(let ((new-table (tea::make-table)))
	  (setf (tea::table-entry table key1) new-table)
	  (setf (tea::table-entry new-table key2) new-value))))))

(%defsetf tea::two-d-table-entry tea::two-d-table-entry-setter)

(defun tea::walk-two-d-table (proc table)
  (tea::walk-table
   #'(lambda (k1 table-1)
     (tea::walk-table
      #'(lambda (k2 val)
	  (funcall (closure proc) k1 k2 val))
      table-1))
   table))

(setf-value-and-function 'tea::make-two-d-table (function tea::make-table))

;;;(defun tea::make-two-d-table (&optional id)
;;;   (let ((tbl (tea::make-hash-table #'equal id)))
;;;      (setf (safe-table-type tbl) 'two-d-table)
;;;      tbl))
;;;
;;;(defun tea::two-d-table-entry (table key1 key2)
;;;  (let ((key (cons key1 key2)))
;;;    (let ((deferred (assoc key 
;;;			   (safe-table-deferred table)
;;;			   :test (safe-table-test table))))
;;;      (if deferred (cdr deferred)
;;;	(gethash key (safe-table-table table))))))
;;;
;;;
;;;(defun two-d-table-entry-setter (table key1 key2 value)
;;;   (table-entry-setter table (cons key1 key2) value))
;;; 
;;;(%defsetf tea::two-d-table-entry  two-d-table-entry-setter)
;;;
;;;(defun tea::walk-two-d-table (proc table)
;;;  (tea::walk-table
;;;   #'(lambda (k val)
;;;       (funcall proc (car k) (cdr k) val))
;;;   table))

(setf-value-and-function 'tea::table-hash (function sxhash))

(defun tea::copy-table (table id &optional (proc #'tea::identity))
  (let ((new (copy-safe-table table))
	(new-real-table (make-hash-table :test (safe-table-test table))))
    (setf (safe-table-table new) new-real-table) 
    (setf (safe-table-id new) id)
    (maphash #'(lambda (k v) (setf (gethash k new-real-table) (funcall 
							       (closure  proc) v)))
	     (safe-table-table table))
    new))

(setf-value-from-function 'tea::copy-table)

(defun tea::recursively-copy-table (table id)
  (labels ((proc (o)
		 (if (tea::hash-table? o)
		     (rec-copy o)
		   o))
	   (rec-copy (o) (tea::copy-table o id #'proc)))
    (rec-copy table)))
    
;;modified Wed Dec 10 14:02:14 EST 1997 by jt.
;;This makes printing much more informative.

(defvar *display-object-to-index-table* nil)
(defvar *display-index-to-object-table* nil)
;;;
(defvar *last-displayed-index* 0)


;;(defun tea::object-hash (x) (sxhash x))
;;;  (or (gethash x *display-object-to-index-table*)
;;;      (progn (incf *last-displayed-index*)
;;;	     (setf (gethash *last-displayed-index* *display-index-to-object-table*) x)
;;;	     (setf (gethash x *display-object-to-index-table*) *last-displayed-index*)
;;;	     *last-displayed-index*)))

(setf-value-and-function 'tea::object-hash #'sxhash)

(defun tea::object-unhash (index) 
  (if  *display-index-to-object-table*
      (gethash index *display-index-to-object-table*)
    index))

(setf-value-from-function 'tea::object-unhash)
