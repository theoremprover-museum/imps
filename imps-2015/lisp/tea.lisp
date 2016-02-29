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

(eval-when (compile load eval)
  (import (mapcar #'(lambda (x) (find-symbol x "TEA-IMPLEMENTATION"))
		  '(

		    ;;Defined in TEA-IMPLEMENTATION
			      

		    "SELECT"
		    "DESTRUCTURE"
		    "PROGNIFY" 
		    "OBJECT-CLOSURE"
		    "STYPE-MASTER"
		    "OBJECT?"
		    "OPERATION?"
		    "SWITCH?"
		    "CONCATENATE-SYMBOL"
		    "SETTER"
		    "CALL"
		    "OBJECT-DEFAULT"
		    "OBJECT-HANDLERS"
		    "MAKE-OBJECT"
		    "OOL"
		    "JOIN"
		    "=>"
		  
		    "QUOTE"

		    "DO"
		    "LET"
		    "LET*"
		    "UNWIND-PROTECT"
		    "MACROEXPAND"
		    "TRACE"
		    "UNTRACE"
		    "FUNCTION"
		    "CATCH"
		    "THROW"

;;The symbol is T is treated differently., as a variable whose VALUE
;;is the usual symbol t.  The reason is that t cannot be reset in some lisps
;;(such as clisp), even in let forms.
;;NIL should be treated similarly. The value of tea::nil is lisp::nil.
		  
;;		  "NIL"
		    "*DEFAULT-PATHNAME-DEFAULTS*"
		    "IN-PACKAGE"


		    ))
	  (find-package "TEA")

	  ))
