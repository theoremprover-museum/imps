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


;;(require 'font-lock) ;;load it first!

(cond ((and window-system (v19-fsf-p))
       (require 'font-lock);;
       (setq imps-font-lock-keywords '(("^(def[-a-z]+\\s +\\([^ ]+\\)" 1
					font-lock-function-name-face)))


       (setq font-lock-default-alist
	     (list
	      (cons 'scheme-mode imps-font-lock-keywords))))
      ((and window-system (v19-lucid-p))

       (require 'font-lock);; (load it first!)
       (copy-face 'font-lock-function-name-face 'font-lock-def-form-name-face)
       (copy-face 'font-lock-keyword-face 'font-lock-def-form-face)
       (setq imps-font-lock-keywords
	     '(("^(\\(def[-a-z]+\\)\\s +\\([^
]+\\)" (1 font-lock-def-form-face) (2 font-lock-def-form-name-face))))

       (make-face 'font-lock-grounded-face)

       (set-face-foreground 'font-lock-grounded-face "white")
       (set-face-background 'font-lock-grounded-face "dark green")

       (make-face 'font-lock-hanging-face)
       (set-face-foreground 'font-lock-hanging-face "black")
       (set-face-background 'font-lock-hanging-face "PaleVioletRed")
       (make-face 'font-lock-sqn-face)
       
       (set-face-foreground 'font-lock-sqn-face "midnight blue")
       (set-face-background 'font-lock-sqn-face "LightSlateGray")
       (make-face 'font-lock-inference-face)
       
       (set-face-foreground 'font-lock-inference-face "black")
       (set-face-background 'font-lock-inference-face "green")
       (setq dg-font-lock-keywords
	     '(("^.*\\(IMPS.*GROUNDED\\).*$" (1 font-lock-grounded-face))
	       ("^.*\\(IMPS-SQN.*see[ ]*above-\\).*$" (1 font-lock-grounded-face))
	       ("^.*\\(IMPS-SQN-[0-9]*\\))" (1 font-lock-hanging-face))
	       ("^.*\\(IMPS-SQN-[0-9]*\\)" (1 font-lock-sqn-face))
	       ("[-0-9a-zA-Z]" (0 font-lock-inference-face))))
       (put 'dg-mode 'font-lock-defaults (list 'dg-font-lock-keywords nil t nil nil))
       (put 'scheme-mode 'font-lock-defaults (list 'imps-font-lock-keywords nil t nil nil))))

'(defconst imps-font-lock-keywords
  '(("^(def[-a-z]+\\s +\\([^
]+\\)" 1 font-lock-function-name-face)))

'(setq font-lock-string-face 'italic)
'(setq font-lock-function-name-face 'bold-italic)
'(setq lisp-font-lock-keywords lisp-font-lock-keywords-2)
'(set-face-underline-p font-lock-string-face nil)

'(cond ((v19-lucid-p)
       (defun font-lock-set-defaults ()
	 "sets font-lock-keywords to something appropriate for this mode."
	 (setq font-lock-keywords
	       (if (memq major-mode '(lisp-mode scheme-mode)) 
		   (nconc font-lock-keywords '(("^(def[-a-z]+\\s +\\([^
]+\\)" (1 font-lock-function-name-face))))))))
      ((v19-fsf-p)
       (defun font-lock-set-defaults ()
	 "sets font-lock-keywords to something appropriate for this mode."
	 (setq font-lock-keywords
	       (if (memq major-mode '(lisp-mode scheme-mode)) 
		   (nconc font-lock-keywords '(("^(def[-a-z]+\\s +\\([^
]+\\)" 1 font-lock-function-name-face))))))))


      

(provide 'imps-font-lock)

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    
