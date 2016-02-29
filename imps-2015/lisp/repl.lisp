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

(defvar tea::err-** nil)

(defvar *repl-print* 
  #'(lambda (obj) (tea::print obj (tea::standard-output))))
(defvar *repl-read*
  #'(lambda () (tea::read (tea::standard-input))))
(defvar *repl-eval* #'(lambda (obj) (eval obj)))
(defvar *repl-prompt* "OOL> ")
(defvar *repl-err* (tea::error-output))

(defun tea::error (&rest err-args)
  (setq tea::err-** err-args)
  (apply (tea::signal-error-procedure) err-args))

(setf-value-and-closure
 (build-switch 'tea::signal-error-procedure
	       (function error)
	       tea::procedure?))

(setf-value-from-function 'tea::error)

(defun ool ()
  (let ((*package* (find-package "TEA"))
	(tea::** '()))
    (loop
     (tea::display (tea::repl-prompt)  (tea::standard-output) )
     (setq tea::**
	   (funcall (tea::repl-print)
		    (funcall (tea::repl-eval)
			     (funcall (tea::repl-read)))))
     (tea::format (tea::standard-output) "~%"))))


(defun tea::repl-print () *repl-print*)
(defun set-repl-print (proc) (setf *repl-print* proc))
(%defsetf tea::repl-print set-repl-print)

(defun tea::repl-read () *repl-read*)
(defun set-repl-read (proc) (setf *repl-read* proc))
(%defsetf tea::repl-read set-repl-read)

(defun tea::repl-eval () *repl-eval*)
(defun set-repl-eval (proc) (setf *repl-eval* proc))
(%defsetf tea::repl-eval set-repl-eval)

(defun tea::repl-prompt () *repl-prompt*)

(defun set-repl-prompt (str)
    (setq *repl-prompt* str))

(%defsetf tea::repl-prompt set-repl-prompt)

(init-reader (tea::port-read-table (tea::standard-input)))
;;(ool-reset-macro #\@)
;;(ool)
