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

;;; functions to use lists as sets 

(defun tea::is-set? (set)
  (do ((l set (cdr l)))
      ((null l) 't)
    (if (member (car l) (cdr l)) (return '()))))
(setf-value-from-function 'tea::is-set?)
(defun tea::make-set (lst)
  (remove-duplicates lst :test #'eql))

(defun tea::make-singleton (elem)
  (list elem))

(defvar tea::the-empty-set '())

(setf-value-and-function 'tea::empty-set? (function null))
(setf-value-and-function 'tea::first-set-element (function car))
(setf-value-and-function 'tea::rest-of-set (function cdr))
(setf-value-and-function 'tea::element-of-set? (function member))
(setf-value-and-function 'tea::add-set-element (function adjoin))
(setf-value-and-function 'tea::delete-set-element (function remove))
(setf-value-and-function 'tea::subset? (function subsetp))

(defun tea::subset-with-pred? (pred set1 set2)
  (subsetp set1 set2 :test pred))

(defun tea::subset-with-equal? (set1 set2)
  (subsetp set1 set2 :test #'equal))
(setf-value-from-function 'tea::subset-with-equal?)

(defun tea::set-equal? (set1 set2)
  (and 
   (subsetp set1 set2)
   (subsetp set2 set1)))
(setf-value-from-function 'tea::set-equal?)

(defun tea::proper-subset? (set1 set2)
  (and (subsetp set1 set2)
       (not (subsetp set2 set1))))

(defun tea::set-equal-with-pred? (pred set1 set2)
  (and 
   (subsetp set1 set2 :test pred)
   (subsetp set2 set1 :test pred)))

(defun tea::set-equal-with-equal? (set1 set2)
  (and 
   (subsetp set1 set2 :test #'equal)
   (subsetp set2 set1 :test #'equal)))

(setf-value-from-function 'tea::set-equal-with-equal?)
;;(setf-value-from-function 'tea::set-equal?)


(setf-value-and-function 'tea::equal-sets? (function tea::set-equal?))

(setf-value-and-function 'tea::set-union (function union))
(setf-value-and-function 'tea::set-intersection (function intersection))
(setf-value-and-function 'tea::intersection (function intersection))
(setf-value-and-function 'tea::union (function union))
(setf-value-and-function 'tea::set-diff (function set-difference))
(setf-value-and-function 'tea::set-difference (function set-difference))



