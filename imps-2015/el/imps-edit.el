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

(provide 'imps-edit)
;;;(require 'scheme)

(defconst assumption-assertion-separator "=>")
(defconst assumption-assertion-separator-pattern
  (concat "^\\s *" assumption-assertion-separator))

(defvar sequent-edit-mode-map
  (let ((map (copy-keymap scheme-mode-map)))
    ;;(define-key map "\C-c\C-c" 'imps-post)

    ;;this may be unsatisfactory.

    (define-key map "\C-c\C-c" 'imps-post) 
    map))

(defun sequent-edit-mode ()
  "Major mode for editing sequent nodes for IMPS deduction graphs.
Commands:
\\{sequent-edit-mode-map}\n"
  (kill-all-local-variables)
  (use-local-map sequent-edit-mode-map)
  (setq major-mode 'sequent-edit-mode)
  (setq mode-name "Sequent Edit")
;;  (setq dg-number 1) ;; vestigial
  (setq reference-sqn (current-sqn-no))
  (setq buffer-read-only nil)
  (scheme-mode-variables)
  (run-hooks 'dg-mode-hook))


(defun imps-post ()
  "Send contents of buffer to IMPS process to post in deduction-graph"
  (interactive)
  (if (not (balance-defuns (current-buffer)))
      (error "Unbalanced defun."))
  (let* ((text  (buffer-substring (point-min) (point-max)))
	 (context-end (string-match
		       assumption-assertion-separator-pattern
		       text))
	 (assertion-start (match-end 0)))
    (tea-eval-and-update-sqn-and-dg
     (format "(deduction-graph-apply-command
       (name->command 'edit-and-post-sequent-node) (list (sequent-unhash  %s)) (list \"%s\" \"%s\"))" 
	     reference-sqn 
	     (substring text 0 context-end)
	     (substring text assertion-start)))
    (bury-buffer)
    (set-window-configuration imps-edit-window-configuration)))

(defun imps-read-and-start-deduction ()
 "Start new IMPS deduction with contents of current buffer as goal."
  (interactive)
  (if (not (balance-defuns (current-buffer)))
      (error "Unbalanced defun."))
  (let* ((text  (buffer-substring (point-min) (point-max)))
	 (context-end (string-match
		       assumption-assertion-separator-pattern
		       text))
	 (assertion-start (match-end 0))
	 (empty-context (string-match "Empty-context"
				      (substring text 0 context-end))))
    (if (null context-end)
	(error
	 "Need sequent not formula.  Please put %s in front of assertion."
	 assumption-assertion-separator))
    (tea-eval-large-expression
     (format "(clear-em) (read-sequent-and-start-emacs-deduction \"%s\" \"%s\")"
	     (if empty-context
		 ""
	       (substring text 0 context-end))
	     (substring text assertion-start)))))

;;; (defvar sqn-edit-file-name (expand-file-name
;;;			    (in-vicinity imps-source-files "../tmp/sqn-edit-file.sqn"))
;;;   "File to get fully parenthesized text of sequent node from.")

(defun sqn-edit-from-file (sqn-index sqn-edit-file-name)
  "Retrieve text of sqn to edit in *IMPS Sequent*.  "
  (let ((buff (get-buffer-create "*IMPS Sequent*")))
    (set-buffer buff)
    (erase-buffer)
    (setq reference-sqn sqn-index)
    (insert-file-contents (expand-file-name (substitute-in-file-name sqn-edit-file-name)))
    (sequent-edit-mode)
    (goto-char (point-max))))

;(defun imps-edit-goal (buffer)
;  (interactive  "BBuffer to construct goal sequent in: ")
;  (pop-to-buffer buffer)
;  (erase-buffer)
;  (scheme-mode)
;  (insert "Empty-context\n =>\n[Goal]"))

;;;(defconst separator-for-expression-editing "^[ \t]*$")
;;;
;;;(defvar expression-edit-mode-map
;;;  (let ((map (copy-keymap scheme-mode-map)))
;;;    (define-key map "\C-c\C-c" 'expression-edit-finished)
;;;    (define-key map "\C-cx" 'expression-xview)
;;;    map))
;;;
;;;(defun expression-edit-mode ()
;;;  "Major mode for editing expressions.
;;;Commands:
;;;\\{expression-edit-mode-map}\n"
;;;  (kill-all-local-variables)
;;;  (use-local-map expression-edit-mode-map)
;;;  (setq major-mode 'expression-edit-mode)
;;;  (setq mode-name "Expression Edit")
;;;  (setq buffer-read-only nil)
;;;  (scheme-mode-variables)
;;;  (run-hooks 'dg-mode-hook))
;;;
;;;(defun imps-build-expression ()
;;;  "Builds expression.    "
;;;  (interactive)
;;;  (setq imps-edit-window-configuration (current-window-configuration))
;;;  (pop-to-buffer (get-buffer-create "*IMPS Expression*"))
;;;  (expression-edit-mode)
;;;  (goto-char (point-max))
;;;  (message "Enter formula and C-c C-c when finished."))

(defun imps-build-expression ()
  "Build an imps expression.    "
  (interactive)
  (let ((input
	 (let ((x-process-mouse-hook (if (and (featurep 'imps-x-support)
					      (boundp 'expression-grabber-mouse-hook))
					 expression-grabber-mouse-hook
				       nil)))

	   (imps-read-from-minibuffer "Expression: " nil inferior-tea-minibuffer-map))))

    (let ((val (get-literal-from-tea (format "(qr-safe-reference %s)"
					     (imps-input-quote-string-if-needed input)))))
      (if (numberp  val)
	  (message (format "imps-ref=%s" val))
	(progn (message "Invalid syntax.")
	       (imps-error val))))))

;;(defun imps-expression-at-point ()
;;  (let (beg end)
;;    (save-excursion
;;      (let ((search-beg (re-search-backward separator-for-expression-editing (point-min) 't)))
;;	(setq beg (if search-beg (point) (point-min)))))
;;    (save-excursion
;;      (let ((search-end (re-search-forward separator-for-expression-editing (point-max) 't)))
;;	(setq end (if search-end (match-end 0) (point-max)))))
;;    (cons (buffer-substring beg end) end)))

;;;(defun imps-expression-at-point ()
;;;  (save-excursion
;;;    (let* ((beg
;;;	    (progn
;;;	      (re-search-backward separator-for-expression-editing (point-min) 1)
;;;	      (point)))
;;;	   (end
;;;	    (progn
;;;	      (goto-char (end-of-whitespace (point)))
;;;	      (re-search-forward separator-for-expression-editing (point-max) '1)
;;;	      (point))))
;;;      (cons (buffer-substring beg end) end))))
;;;
;;;(defun expression-edit-finished (arg)
;;;  (interactive "P")
;;;  (let ((text-and-end (imps-expression-at-point)))
;;;    (tea-eval-expression
;;;     (format "(bind (((use-quasi-constructor-form?) %s)) (build-expression-for-emacs %d \"%s\"))"
;;;	     (if arg "'#f" "'#t") 
;;;	     (cdr text-and-end)
;;;	     (car text-and-end)))))

(defun expression-xview (arg)
  (interactive "P")
  (let (beg end)
    (let ((text-and-end (imps-expression-at-point)))
      (tea-eval-expression
       (format "(bind (((use-quasi-constructor-form?) %s)) 
                  (xview (qr \"%s\")))"
	       (if arg "nil" "t") (car text-and-end))))))

(defun emacs-display-expression (pos str)
  (pop-to-buffer (get-buffer-create "*IMPS Expression*"))
  (goto-char pos)
  (insert "\n\n")
  (insert str))

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    
