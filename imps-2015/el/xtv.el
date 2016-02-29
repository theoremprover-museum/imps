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
; 
; 
; COPYRIGHT NOTICE INSERTED: Mon Mar  3 15:51:48 EST 1997

;; Modification by W. M. Farmer Mon Mar 22 2004
;; "send-string" replaced with "process-send-string".


(provide 'xtv)

(defvar xtv-program-name "xtv"
  "Name of the program used by the X windows interactive previewer." )

(defun xtv ()
  (interactive)
  (cond ((and (get-buffer "*xtv-shell*") (get-process "xtv-shell"))
	 (quit-process "xtv-shell" t))
	(t (require 'shell)
	   (process-kill-without-query
	    (get-buffer-process (make-shell "xtv-shell" "csh")))
	   (sleep-for 1)))
  (process-send-string "xtv-shell"
	       (format "%s -s 2 -topmargin 0 < %s\n"
		       xtv-program-name
		       "/tmp/delete_me.tex")))

(defun xtv-region (beg end)
  "apply tex to this region."
  (interactive "r")
  (xtv-string (buffer-substring beg end)))

(defun xtv-string (str)
  "apply tex to this string."
  (process-send-string "xtv-shell" (format "%s\f\n" str)))

(defun xtv-kill ()
  (interactive)
  (quit-process "xtv-shell" t))





    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    
