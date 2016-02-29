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


;;These are added for extensionof TEA but are not needed for IMPS 

(eval-when (eval compile load)
	   
(defmacro def-value-from-macro (sym arglist)
  `(setf (symbol-value ',sym) (function (lambda ,arglist (,sym ,@arglist)))))



(def-value-from-macro tea::not-negative? (x))
(def-value-from-macro tea::not-positive? (x))
(def-value-from-macro tea::>=0? (x))
(def-value-from-macro tea::<=0? (x))
(def-value-from-macro tea::string-empty? (str))
(def-value-from-macro tea::string-tail (l))
(def-value-from-macro tea::char (str))
(def-value-from-macro tea::nth (l n) )
(def-value-from-macro tea::nthcdr (l n) )
;(def-value-from-macro tea::walk (fn &rest ls))
;(def-value-from-macro tea::map (fn &rest ls))
(def-value-from-macro ->boolean (arg))
;(def-value-from-macro tea::any (fn &rest ls))
;(def-value-from-macro tea::any? (fn &rest args))
;(def-value-from-macro tea::every (fn &rest ls))
;(def-value-from-macro tea::every? (fn &rest args))
(def-value-from-macro tea::map! (fn l))
;(def-value-from-macro tea::everycdr? (fn &rest lists))
;(def-value-from-macro tea::anycdr? (fn &rest lists))
(def-value-from-macro tea::string-posq (obj l))
(def-value-from-macro tea::posq (obj l))
(def-value-from-macro tea::pos (pred obj l))
(def-value-from-macro tea::lastcdr (l))
(def-value-from-macro tea::last (l))
(def-value-from-macro tea::memq (obj ls))
(def-value-from-macro tea::memq? (obj ls))
(def-value-from-macro tea::mem? (pred object list))
(def-value-from-macro tea::mem (pred object list))
(def-value-from-macro tea::delq (object list))
(def-value-from-macro tea::del (pred object list))
(def-value-from-macro tea::delq! (object list))
(def-value-from-macro tea::del! (pred object list))
(def-value-from-macro tea::assq (object list))
(def-value-from-macro tea::assq? (object list))
(def-value-from-macro tea::ass (pred object list))
(def-value-from-macro tea::list->string (l))
(def-value-from-macro tea::string->list (l))
(def-value-from-macro tea::make-vector (n))
(def-value-from-macro tea::list->vector (l))
(def-value-from-macro tea::vector->list (v))
(def-value-from-macro tea::char->string (char))
(def-value-from-macro tea::sort-list (l pred))
(def-value-from-macro tea::fixnum? (i))
(def-value-from-macro tea::ratio? (r))
;(def-value-from-macro tea::remove-duplicates (predicate une-liste &optional from-end))
)
