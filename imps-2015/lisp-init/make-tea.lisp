;! /bin/sh
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

; /bin/sh
;; Create a new executable dump of Tea Emulator in GNU Common Lisp.  

(defun compile-tea-files (&optional (imps-directory "~/imps"))
  (let* ((lisp-directory (format nil "~A/lisp" imps-directory))

	 (tea-files '("packages"
		     "tea-implementation"
		     "tea"
		     "basic"
		     "supplements" 
		     "sets"
		     "special-forms"
		     "operations"
		     "structures"
		     "definitions"
		     "ports"
		     "wrappers"
		     "hash"
		     "filesystem"
		     "initialization"
		     "repl")))
    (mapc 
     (function (lambda (x) 
		 (compile-file (truename  (format nil "~A/~A.lisp" lisp-directory  x)))))
     tea-files)	))


(defun make-tea-dump (&optional (imps-directory "~/imps"))
  (let* ((lisp-directory (format nil "~A/lisp" imps-directory))
	 (tea-files '("packages"
		     "tea-implementation"
		     "tea"
		     "basic"
		     "supplements" 
		     "sets"
		     "special-forms"
		     "operations"
		     "structures"
		     "definitions"
		     "ports"
		     "wrappers"
		     "hash"
		     "filesystem"
		     "initialization"
		     "repl")))
    (mapc (function (lambda (x) (load (truename (format nil "~A/~A.fas"  lisp-directory x)))))
	  tea-files)
    (ext:saveinitmem 
     (format nil "~A/../executables/tea" lisp-directory) 
     :executable 't  
     :start-package (find-package "TEA"))))



    

    

    

    

    

    

    

    
