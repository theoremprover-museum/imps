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


(provide 'imps-commands)

(defvar command-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map "e" 'apply-line)
    (define-key map "!" 'apply-line)
    (define-key map "q" 'quit-command-menu)
    (define-key map "?" 'imps-manual-command-line)
    (define-key map "m" 'apply-line)
    map))

(defvar *imps-buffer-menu-type* nil)

(defun dg-command-mode (buffer window-configuration sqn-no)
  "Major mode for interactively working on a deduction graph:
\\{dg-command-mode-map}\n"
  (kill-all-local-variables)
  (use-local-map command-mode-map)
  (make-variable-buffer-local '*imps-buffer-menu-type*)
  (setq major-mode 'dg-command-mode)
  (setq mode-name "IMPS Command Menu")
  (setq command-menu-sqn-no sqn-no)
  (setq parent-buffer buffer)
  (setq parent-configuration window-configuration)
  (setq buffer-read-only 't)
  (scheme-mode-variables)
  (run-hooks 'dg-command-mode-hooks))

(defun apply-line ()
  (interactive)
  (cond ((eq *imps-buffer-menu-type* 'command-menu) (apply-command-line))
	((eq *imps-buffer-menu-type* 'macete-menu) (apply-macete-line))
	(t nil)))
	

(defun command-or-macete-on-current-line ()
  (save-excursion
    (let* ((beg (progn (beginning-of-line) (skip-chars-forward " \t") (point)))
	   (end (progn (if (re-search-forward "\\( \\|\t\\|\n\\)" (point-max) t)
			   (match-beginning 0)
			 beg))))
      (buffer-substring beg end))))

(defun apply-command-line ()
  (interactive)
  (let ((sqn-no command-menu-sqn-no)
	(cline (command-or-macete-on-current-line)))
    (if (string= cline "")
	(error "No command is applicable.")
      (let ((form (car (read-from-string (format "(dg-apply-command \"%s\" '(%d))"
						 cline
						 sqn-no)))))
	(bury-buffer)
	(set-window-configuration parent-configuration)
	(set-buffer parent-buffer)
	(eval form)))))

(defun imps-manual-command-line ()
  (interactive)
  (let ((sqn-no command-menu-sqn-no)
	(cline (command-or-macete-on-current-line)))
    (if (string= cline "")
	(error "No command is applicable.")
      (let ((form (car (read-from-string (format "(imps-manual-entry \"%s\")"
						 cline)))))
	(bury-buffer)
	(set-window-configuration parent-configuration)
	(set-buffer parent-buffer)
	(eval form)))))

(defun imps-command-menu ()
  (interactive)
  (let ((sqn-no (current-sqn-no))
	(config (current-window-configuration))
	(save-buffer (current-buffer))
	(buffer (get-buffer-create "*IMPS Commands*")))
    (message "Updating Command Menu...")
    (let ((commands 
	   (mapconcat '(lambda (x) x)
		      (get-literal-from-tea 
		       (format "(applicable-commands (sequent-unhash %d))" sqn-no))
		      "\n")))
		      
      (message "Done")
      (set-buffer buffer)
      (pop-to-buffer buffer)
      (setq buffer-read-only nil)
      (erase-buffer)
      (insert commands)
      (dg-command-mode save-buffer config sqn-no)
      (setq *imps-buffer-menu-type* 'command-menu)
      (goto-char (point-min)))))

(defun imps-special-command-menu ()
  (interactive)
  (let ((sqn-no (current-sqn-no))
	(config (current-window-configuration))
	(save-buffer (current-buffer))
	(buffer (get-buffer-create "*IMPS Special Commands*")))
    (message "Updating Special Command Menu...")
    (let ((commands 
	   (mapconcat '(lambda (x) x)
		      (get-literal-from-tea 
		       (format "(applicable-special-commands (sequent-unhash %d))" sqn-no))
		      "\n")))
		      
      (message "Done")
      (set-buffer buffer)
      (pop-to-buffer buffer)
      (setq buffer-read-only nil)
      (erase-buffer)
      (insert commands)
      (dg-command-mode save-buffer config sqn-no)
      (setq *imps-buffer-menu-type* 'command-menu)
      (goto-char (point-min)))))

(defun apply-macete-line ()
  (interactive)
  (let ((sqn-no command-menu-sqn-no)
	(cline (command-or-macete-on-current-line)))
    (if (string= cline "")
	(error "No macete is applicable."))
    (let ((form
	   (format
	    "(deduction-graph-apply-command
                 (name->command '%s) 
                 (list (sequent-unhash %d)) 
                 (list (name->macete '%s)))"
	    (if current-prefix-arg
		'apply-macete
	      'apply-macete-with-minor-premises)
	    sqn-no
	    cline)))
      (bury-buffer)
      (set-window-configuration parent-configuration)
      (set-buffer parent-buffer)
      (tea-eval-and-update-sqn-and-dg form))))

;;;(defun describe-macete-line ()
;;;  (interactive)
;;;  (let ((sqn-no command-menu-sqn-no)
;;;	(dg-no dg-number)
;;;	(cline (command-or-macete-on-current-line)))
;;;    (if (string= cline "")
;;;	(error "No macete is applicable."))
;;;    (save-excursion
;;;      (let ((str
;;;	      (get-literal-from-tea (format "(macete-description '%s)" cline))))
;;;	(let* ((beg (progn (beginning-of-line) (skip-chars-forward " \t") (point)))
;;;	       (end (progn (if (re-search-forward "\\( \\|\t\\|\n\\)" (point-max) t)
;;;			       (match-beginning 0)
;;;			     beg)))
;;;	     
;;;      (buffer-substring beg end)))

(defun quit-command-menu ()
  (interactive)
  (bury-buffer)
  (set-window-configuration parent-configuration)
  (set-buffer parent-buffer))

(defun imps-macete-menu (&optional arg)
  (interactive)
  (let ((sqn-no (current-sqn-no))
	(config (current-window-configuration))
	(save-buffer (current-buffer))
	(buffer (get-buffer-create "*IMPS Macetes*")))
    (tea-eval-expression
     (format "(find-applicables-with-latex-description (sequent-unhash %d))" sqn-no))
    (let ((macete-number
	   (read-from-minibuffer "Macete number (Please await tex output): " nil nil t)))
      (tea-eval-and-update-sqn-and-dg
       (format
	"(deduction-graph-apply-command
	  (name->command 'apply-macete-with-minor-premises) 
	  (list (sequent-unhash %d)) 
	  (list (nth (last-applicables) %d)))"
	sqn-no (1- macete-number))))))

(defun imps-macete-menu-xless (&optional arg)
  (interactive)
  (let ((sqn-no (current-sqn-no))
	(config (current-window-configuration))
	(save-buffer (current-buffer))
	(buffer (get-buffer-create "*IMPS Macetes*")))
    (message "Updating Macete Menu...")
    (let ((commands 
	   (mapconcat '(lambda (x) x)
		      (get-literal-from-tea 
		       (format "(applicable-macetes-for-sqn-with-description (sequent-unhash %d))"
			       sqn-no))
		      "\n")))
		      
      (message "Done")
      (set-buffer buffer)
      (pop-to-buffer buffer)
      (setq buffer-read-only nil)
      (erase-buffer)
      (insert commands)
      (dg-command-mode save-buffer config sqn-no)
      (setq *imps-buffer-menu-type* 'macete-menu)
      (goto-char (point-min)))))

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    
