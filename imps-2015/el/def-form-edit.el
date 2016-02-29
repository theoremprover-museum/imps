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


(defvar df-regexp
  "^(\\(\\(def\\|load\\|include\\)-[a-zA-Z---]+\\)")
(defvar df-height 7)
(defvar df-number-regexp
  "^[ ]*\\([0-9]*\\)")
(defvar df-regexp-line
  "\\(\\(def\\|load\\|include\\)-[a-zA-Z---]+ .*\\)$")
(defvar df-prefix-string
  "%")
(defvar df-impose-single-frame
  t
  "If non-nil, use single frame for def-form list and main buffer.
Default:  t.")

(define-key scheme-mode-map "\C-c:" 'df-list-create-or-restore)

(defvar df-list-map
  (let ((map (make-sparse-keymap)))
    (define-key map "." 'df-show-current-def-form)
    (define-key map ":" 'df-show-current-def-form)
    (define-key map "n" 'df-show-next-def-form)
    (define-key map "p" 'df-show-previous-def-form)
    (define-key map "\C-cp" 'df-insert-def-form-template-before)
    (define-key map "\C-cn" 'df-insert-def-form-template-after)
    (define-key map "q" 'df-quit)
    (define-key map "e" 'df-evaluate-def-form)
    (define-key map " " 'df-page-def-form)
    (define-key map "\er" 'df-refresh-listing)
    (define-key map "\177" 'df-page-back-def-form)
    map))

(defvar df-buffer-listing-alist '())

(defun df-get-df-list (buff)
  (cdr (assq buff df-buffer-listing-alist)))

(defun df-put-df-list (buff df-list)
  (setq df-buffer-listing-alist 
	(cons (cons buff df-list) df-buffer-listing-alist)))

(defun df-listing-mode (buff config)
  "Major mode for listing def-forms in a buffer."
  (kill-all-local-variables)
  (use-local-map df-list-map)
  (make-variable-buffer-local 'df-main-buffer)
  (make-variable-buffer-local 'df-previous-window-config)
  (setq mode-line-buffer-identification (quote ("{%b}")))
  (setq major-mode 'df-listing-mode)
  (setq mode-name "DF-List")
  (setq df-previous-window-config config)
  (setq df-main-buffer buff)
  (df-put-df-list buff (current-buffer))
  (setq buffer-read-only 't)
  (run-hooks 'df-listing-mode-hook))

;(defun df-listing-mode (buff config)
;  (kill-all-local-variables)
;  (use-local-map df-list-map)
;  (make-variable-buffer-local 'df-main-buffer)
;  (make-variable-buffer-local 'df-previous-window-config)
;  (setq mode-line-buffer-identification (quote ("{%b}")))
;  (setq major-mode 'df-listing-mode)
;  (setq mode-name "DF-List")
;  (setq df-previous-window-config config)
;  (setq df-main-buffer buff)
;  (setq buffer-read-only 't)
;  (run-hooks 'df-listing-mode-hook))
  
(defun df-in-buffer-list ()
  (save-excursion
    (save-restriction
      (widen)
      (goto-char (point-min))
      (let ((accum '())
	    (match-begin nil))
	(while (re-search-forward df-regexp (point-max) t)
	  (setq match-begin (match-beginning 1))
	  (setq accum 
		(cons
		 (buffer-substring match-begin (progn (end-of-line) (point)))
			 
		 accum)))
	(nreverse accum)))))

(defun df-list-in-buffer ()
  "Provide a list of def-forms in current buffer."
  (interactive)
  (let ((dfs (df-in-buffer-list))
	(save (current-buffer))
	(n 1))
    (or dfs (error "No def-forms in buffer!"))
    (set-buffer
     (get-buffer-create  (format "%s%s" df-prefix-string (buffer-name))))
    (setq buffer-read-only nil)
    (erase-buffer)
    (while dfs
      (insert (format "%4s  " n))
      (setq n (+ 1 n))
      (insert (car dfs))
      (setq dfs (cdr dfs))
      (if dfs (newline)))

    (df-listing-mode save (current-window-configuration))
    (goto-char (point-min))
    (set-buffer (current-buffer))
    (df-show-current-def-form)))

(defun df-refresh-listing ()
  (interactive)
  (set-buffer df-main-buffer)
  (widen)
  (let* ((here (point))

    ;;counting occurrences backwards

	(occurrences
	   (let ((count 0)
		 (beg (point-min)))
	     (end-of-line)
	     (while (re-search-backward df-regexp beg t)
	       (setq count (1+ count)))
	     count)))
    (df-list-in-buffer)
    (df-show-numbered-def-form occurrences)
    (goto-line occurrences)))

(defun df-show-next-def-form ()
  "Show def-form on next line."
  (interactive)
  (forward-line 1)
  (beginning-of-line)
;  (recenter 't)
  (df-show-current-def-form))

(defun df-show-previous-def-form ()
  "Show def-form on previous line."
  (interactive)
  (forward-line -1)
  (beginning-of-line)            
; (recenter 't)
  (df-show-current-def-form)) 

(defun df-show-current-def-form ()
  "Show def-form cursor is on."
  (interactive)
  (let ((num nil))
    (save-excursion
      (beginning-of-line)
      (looking-at df-number-regexp)
      (setq num (car (read-from-string
		      (buffer-substring (match-beginning 1) (match-end 1))))))
    (df-show-numbered-def-form num)))



;;Referring to def-form by number is not vert robust, as editing in the
;; file can delete def-form regexps, but neither is this

;;;(defun df-show-current-def-form ()
;;;  "Show def-form cursor is on."
;;;  (interactive)
;;;  (let ((num nil))
;;;    (save-excursion
;;;      (beginning-of-line)
;;;;      (set-window-point (selected-window) (point))
;;;      (re-search-forward df-regexp-line (point-max) nil)
;;;      (setq str (buffer-substring (match-beginning 1) (match-end 1))))
;;;    (df-show-def-form-matching-string (concat "^(" str))))

(defun df-show-1 (str num)
  (save-excursion
    (set-buffer df-main-buffer)
    (let ((bufpos (save-excursion 
		    (save-restriction 
		      (widen)
		      (goto-char (point-min))
		      (re-search-forward str (point-max) nil num)
		      (point)))))
      (widen)
      (goto-char bufpos)
      (beginning-of-line)
      (let ((beg (point)))
	(forward-sexp 1)
	(narrow-to-region beg (point))
	(goto-char (point-min)))))
  (df-listing-window-display df-main-buffer (current-buffer)))

;; This procedure takes buffers BOT and TOP displays them in two windows.
;; The top window is selected. 
;; In the case a single frame is not imposed it does the buffers in preferred frames.

;;;changed back to use single frame.

(defun df-listing-window-display (bot top)
  (save-excursion

;;;    (cond
;;;     ((or df-impose-single-frame ;; is always t
;;;	  (not (featurep 'frames)))

    (or (df-check-window-display-and-resize)
	(progn 
	  (delete-other-windows)
	  (split-window-vertically df-height)))

    (let ((win (next-window)))
      (show-buffer win (buffer-name bot))
      (set-window-point win (point-min)))

;;;     ((get-buffer-window bot t)
;;;      (let ((win (get-buffer-window bot t)))
;;;	(set-window-point win (point-min))))
;;;     (t
;;;      (display-buffer-in-preferred-frame bot)
;;;      (let ((win (get-buffer-window bot t)))
;;;	(set-window-point win (point-min)))))
    
    (show-buffer (selected-window) (buffer-name top))
    (recenter t);;(or df-impose-single-frame (/ (window-height) 2))
    ))

;(defun df-show-1 (str num)
;  (let ((save-buf (current-buffer))
;	(main-buf df-main-buffer))
;    (save-excursion
;      (set-buffer df-main-buffer)
;      (let ((bufpos (save-excursion 
;		      (save-restriction 
;			(widen)
;			(goto-char (point-min))
;			(re-search-forward str (point-max) nil num)
;			(point)))))
;	(widen)
;	(goto-char bufpos)
;	(beginning-of-line)
      
;	(let ((beg (point)))
;	  (forward-sexp 1)
;;;	  (skip-syntax-forward " >")
;	  (narrow-to-region beg (point))
;	  (goto-char (point-min)))
;	(cond
;	 ((or df-impose-single-frame
;	      (not (featurep 'frames)))
;	  (or (df-check-window-display-and-resize)
;	      (progn 
;		(delete-other-windows)
;		(split-window-vertically df-height)))
;	  (let ((win (next-window)))
;	    (show-buffer win (buffer-name main-buf))
;	    (set-window-point win (point-min))))
;	 ((get-buffer-window main-buf t)
;	  (let ((win (get-buffer-window main-buf t)))
;	    (set-window-point win (point-min))))
;	 (t
;	  (display-buffer-in-preferred-frame main-buf)
;	  (let ((win (get-buffer-window main-buf t)))
;	    (set-window-point win (point-min)))))))
;    (switch-to-buffer save-buf)
;    (recenter (or df-impose-single-frame (/ (window-height) 2)))))

(defun df-show-def-form-matching-string (str)
  (interactive "p")
  (df-show-1 str 1))

(defun df-show-numbered-def-form (num)
  (interactive "p")
  (df-show-1 df-regexp num))



(defun df-check-window-display-and-resize ()
  (let ((swin (selected-window)))
    (and (eq (next-window (minibuffer-window)) swin)
	 (= 2 (count-windows))
	 (or (= (window-height) df-height)
	     (shrink-window (- (window-height) df-height))
	     't))))



(defun df-page-def-form (arg)
  (interactive "P")
  (scroll-other-window arg))

(defun df-page-back-def-form (arg)
  (interactive "P")
  (if arg
      (scroll-other-window (- arg))
    (scroll-other-window (- (window-height (next-window))))))

(defun df-evaluate-def-form ()
  "Evaluate the def-form cursor is on and flag it as evaluated."
  (interactive)
  (let ((buff (current-buffer)))
    (df-show-current-def-form)
    (set-buffer df-main-buffer)
    (tea-eval-expression
     (buffer-substring (point-min) (point-max)))
    (set-buffer buff)
    (df-flag-entry "E")
    (df-show-next-def-form)))

(defun df-flag-entry (flag)
  (let ((buffer-read-only nil))
    (save-restriction
      (let ((end (progn (end-of-line) (point))))
	(beginning-of-line)
	(re-search-forward df-number-regexp end t)
	(delete-char (length flag))
	(insert flag)))))


(defun df-quit ()
  "Quit df-e.
Restore the previous window
configuration, if one exists.  Finish by running df-quit-hook."
  (interactive)
  (let ((df-main df-main-buffer)
	(df-prev  df-previous-window-config))
    (bury-buffer)

    (if df-prev
	(set-window-configuration df-prev))
    (set-buffer df-main)
    (widen)
    (run-hooks 'df-quit-hook)))


(defun df-insert-def-form-template-before (def-form-name)
  (interactive
   (list
    (completing-read-or-get-from-x-menu
     "Template: " *def-form-template-alist*  nil nil nil)))
  (let ((form (cdr (assoc def-form-name *def-form-template-alist*))))
    
    (let ((num-str nil))
    (save-excursion
      (beginning-of-line)
      (looking-at df-number-regexp)
      (setq  num-str (buffer-substring (match-beginning 1) (match-end 1)))
      (save-excursion
	(df-show-numbered-def-form (car (read-from-string num-str)))

	  (set-buffer df-main-buffer)
	  (goto-char (point-min))
	  (widen)
	  (if form (progn (insert form)
			  (insert "\n\n")))
	  (df-list-in-buffer)))
    (goto-char (point-min))
    (search-forward num-str (point-max) t)
    (df-show-current-def-form))))
      
	  
(defun df-insert-def-form-template-after (def-form-name)
  (interactive
   (list
    (completing-read-or-get-from-x-menu
     "Template: " *def-form-template-alist*  nil nil nil)))
  (let ((form  (cdr (assoc def-form-name *def-form-template-alist*))))
    
    (let ((num-str nil))
      (save-excursion
	(beginning-of-line)
	(looking-at df-number-regexp)
	(setq  num-str (buffer-substring (match-beginning 1) (match-end 1)))
	(save-excursion
	  (df-show-numbered-def-form (car (read-from-string num-str)))

	  (set-buffer df-main-buffer)
	  (goto-char (point-max))
	  (widen)
	  (end-of-line)
	  (if form (progn 	  
		     (insert "\n\n")
		     (insert form)
		     (insert "\n\n")))
	  (df-list-in-buffer)))
      (goto-char (point-min))
      (search-forward num-str  (point-max) t)
      (forward-line 1)
      (df-show-current-def-form))))

;;;(defun df-delete-current-form ()
;;;  (interactive)
;;;    (let ((num-str nil))
;;;      (save-excursion
;;;	(beginning-of-line)
;;;	(looking-at df-number-regexp)
;;;	(setq  num-str (buffer-substring (match-beginning 1) (match-end 1)))
;;;	(save-excursion
;;;	  (df-show-numbered-def-form (car (read-from-string num-str)))
;;;	  (if (yes-or-no-p (format "Delete form %s?" num-str))
;;;	      (progn
;;;		(set-buffer df-main-buffer)
;;;		(delete-region (point-min) (point-max))
;;;		(widen)
;;;		(df-list-in-buffer))))
;;;      (goto-char (point-min))
;;;      (search-forward num-str  (point-max) t)
;;;      (df-show-current-def-form))))

(defun df-find-file (filename)
  (interactive "fFile: ")
  (find-file filename)
  (df-list-in-buffer))


(defun df-list-create-or-restore (&optional refresh)
  (interactive "P")
  (let ((here (point))
	(occurrences
	 (save-excursion
	   (save-restriction
	     (widen)
	     (let ((count 0)
		   (beg (point-min)))
	       (end-of-line)
	       (while (re-search-backward df-regexp beg t)
		 (setq count (1+ count)))

;;If ccurrences is zero, this means point is located on a line BEFORE any
;;def-forms. In this case, begin with first def-form.

	       (max 1 count))))))
    (let ((df-listing (df-get-df-list (current-buffer)))
	  (save (current-buffer)))
      (if (and df-listing (buffer-name df-listing) (null refresh))
	  (progn
	    (narrow-to-current-def-form-def-form)
	    (switch-to-buffer df-listing)
	    (goto-line occurrences)
	    (df-listing-window-display save df-listing)
	    (set-window-point (get-buffer-window save t) here))
	(progn
	  (df-list-in-buffer)
	  (goto-line occurrences)
	  (df-show-numbered-def-form occurrences)
	  (set-window-point (get-buffer-window save t) here))))))

(defun narrow-to-current-def-form-def-form ()
  (interactive)
  (let (beg end)
    (save-excursion
      (save-restriction
	(widen)
	(end-of-line)
	(setq beg
	      (progn
		(or (re-search-backward df-regexp (point-min) 'no-error)
		    (and (re-search-forward df-regexp (point-max) 'no-error)
			 (or (beginning-of-line) t))
		    (error "No def-forms in buffer!"))
		(point)))
	(forward-sexp 1)
	(setq end (point))))
    (narrow-to-region beg end)))

;(defun df-restore-listing-display ()
;  (interactive)
;  (let ((here (point))
;	(save (current-buffer))
;	(occurrences
;	 (save-excursion
;	   (save-restriction
;	     (widen)
;	     (let ((count 0)
;		   (beg (point-min)))
;	       (end-of-line)
;	       (while (re-search-backward df-regexp beg t)
;		 (setq count (1+ count)))
;	       count)))))
;    (df-list-in-buffer)
;    (goto-line occurrences)
;    (df-show-numbered-def-form occurrences)
;    (set-window-point (get-buffer-window save t) here)))


(defun imps-theory-mode ()
  "Major mode for listing def-forms in a buffer."
  (kill-all-local-variables)
  (use-local-map scheme-mode-map)
  (setq major-mode 'scheme-mode)
  (setq mode-name "IMPS Theory")
  (setq buffer-read-only nil)
  (run-hooks 'scheme-mode-hook))


(provide 'def-form-edit)

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    
