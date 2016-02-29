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


(provide 'theory-information)

(defun imps-xview-theorem (theorem)
  "Run xview on the theorem named THEOREM."
  (interactive "sTheorem name: ")
  (tea-eval-expression
   (format "(cond ((name->theorem-1 '%s) => xview)(else (imps-warning \"theorem %s not loaded\")))" theorem theorem)))

(defun imps-xview-macete (macete)
  "Run xview on the macete named MACETE."
  (interactive
   (list (read-macete)))
  (tea-eval-expression
   (format "(cond ((name->macete '%s) => xview) (else (imps-warning \"theorem %s not loaded\")))"
	    macete macete)))

(defun imps-xview-sqns (sqn-nos)
  (interactive
   (list (read-from-minibuffer "Sqn nos: " nil nil nil)))
  (tea-eval-expression
   (format
    "(xview (map (lambda (sqn-no) (sequent-unhash sqn-no)) '(%s)))"
    sqn-nos)))

(defun imps-get-theorem-var-sorts (thm-name)
  (get-literal-from-tea
   (format
    "(theorem-name->var-sort-list '%s)"
    thm-name)))

(defconst macete-minibuffer-map (copy-keymap minibuffer-local-map))
(define-key macete-minibuffer-map " " 'insert-complete-macete-name)
(define-key macete-minibuffer-map "C-m" 'insert-complete-macete-name)
  
(defun read-macete ()
  (interactive)
  (let ((minibuffer-local-map macete-minibuffer-map))
    (read-minibuffer "Macete name: ")))

(defun imps-intern-from-current-file ()
  (interactive)
  (balance-defuns-and-save nil)
  (call-process (in-vicinity imps-source-files "../bin/current_tags")
		nil nil nil (buffer-file-name))
  (imps-intern-from-tmp-tags))

(defvar imps-commands nil
  "*The IMPS commands known currently known to emacs, 
presented as a list suitable for completing-read.")
(defconst imps-commands-file
  (in-vicinity imps-source-files "../etc/imps-commands"))
(defun imps-read-commands-from-file ()
  (let ((tmp-buff (get-buffer-create " *imps-commands-tmp*")))
    (set-buffer tmp-buff)
    (erase-buffer)
    (if (file-readable-p imps-commands-file)
	(insert-file imps-commands-file)
      (error "IMPS command file unreadable.  Try executing (t-e-write-commands) in IMPS."))
    (goto-char (point-min))
    (setq imps-commands
	  (read (current-buffer)))))

(defun add-imps-command (command-string retrieval-protocol-symbol)
  (setq imps-commands
	(cons
	 (list command-string retrieval-protocol-symbol 
	       'default-argument-transmission-protocol)
	 imps-commands)))

(imps-read-commands-from-file)


    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    
