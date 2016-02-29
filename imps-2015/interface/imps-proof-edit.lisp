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


;; Support for building and editing proof scripts.

;;;(require 'process-filter)
(provide 'imps-proof-edit)


;(define-key scheme-mode-map "\C-c!" 'imps-assistant-apply-command)
;(define-key scheme-mode-map "\C-c&" 'imps-assistant-insert-command)
(define-key global-map "\C-cx" 'imps-run-current-proof-script)
(define-key global-map "\C-cr" 'imps-assistant-execute-region)
(define-key global-map "\C-cl" 'imps-assistant-execute-line)
(define-key global-map "\C-cF" 'imps-first-unsupported-relative)
(define-key global-map "\C-ci" 'imps-insert-current-proof)
;;;(defvar *imps-commands* nil)
;;;
;;;(defun subarray (a1 a2)
;;;  (let ((l1 (length a1))
;;;	(l2 (length a2))
;;;	(n 0))
;;;    (and (<= l1 l2)
;;;	 (let ((ans t))
;;;	   (while (< n l1)
;;;	     (if (eq (aref a1 n) (aref a2 n))
;;;		 (setq n (1+ n))
;;;	       (progn (setq ans nil) (setq n l1))))
;;;	   ans))))
;;;
;;;(defun find-completions (string alist)
;;;  
;;;"Takes a STRING and ALIST, a list of entries (str . rest). A completion
;;;is an entry  (str . rest) with str an extension of string. An
;;;exact match is an an entry (str . rest) with str string-equal
;;;to string. Returns all completions unless there is an exact match in which
;;;case it returns just the match."
;;;
;;; (let ((completions nil))
;;;   (catch 'exact-match
;;;     (mapcar '(lambda (x)
;;;		(if (subarray string (car x))
;;;		    (if (string-equal string (car x))
;;;			(progn (setq completions (list x))
;;;			       (throw 'exact-match nil))
;;;		      (setq completions (cons x completions)))))
;;;
;;;	      alist))
;;;    
;;;    completions))
;;;
;;;(defun retrieve-function (command)
;;;  (let ((probe (assoc command *imps-commands*)))
;;;    (cond ((car(cdr probe)))
;;;	  (t 'dg-apply-command))))
;;;
;;;(defun imps-retrieve-commands ()
;;;  (get-literal-from-tea
;;;   "(let ((fuba '())) (walk-table (lambda (k v) (push fuba (list (string-downcase (symbol->string k))))) *COMMAND-TABLE*) fuba)"))
;;;
;;;(defun search-for-completion (string alist)
;;;  (let* ((completions (find-completions string alist))
;;;	 (len (length completions)))
;;;    (cond ((= len 1) (car (car completions)))
;;;	  ((= len 0)
;;;	   (message "Not a discernible command.")
;;;	   nil)
;;;	  (t (completing-read "Ambiguous: " completions nil t string)))))
;;;
;;;(defun imps-command-list ()
;;;  (or *imps-commands* (setq *imps-commands* (imps-retrieve-commands))))

;;;(defun imps-assistant-execute-region ()
;;;  (interactive)
;;;  (set-buffer (or (mode-last-visited-buffer 'scheme-mode)
;;;		  (current-buffer)))
;;;  (let ((beg (region-beginning))
;;;	(end (region-end)))
;;;    (tea-eval-and-update-sqn-and-dg
;;;     (format "(execute-command-sequence (sequent-unhash-in-graph-by-number %d %d) '(%s))"
;;;	     (current-sqn-no) dg-number (buffer-substring-if-balanced-defun beg end)))))

(defun imps-assistant-execute-region ()
  (interactive)
  (set-buffer (or (mode-last-visited-buffer 'scheme-mode)
		  (current-buffer)))
  (let ((beg (region-beginning))
	(end (region-end)))
    (tea-eval-large-expression-and-update-sqn-and-dg
     (format "(execute-command-sequence (sequent-unhash %d) '(%s))"
	     (current-sqn-no) (buffer-substring-if-balanced-defun beg end)))))

(defun buffer-substring-if-balanced-defun (beg end)
  (let ((str (buffer-substring beg end)))
    (if (string-defuns-balanced-p str)
	str
      (error "Unbalanced parentheses."))))

(defun mode-last-visited-buffer (the-mode)
  (save-excursion
    (catch 'found
      (mapcar '(lambda (buff) 
		 (set-buffer buff)
		 (if (and (eq major-mode the-mode)
			  (string-match "^[^ ]" (buffer-name)))
		     (throw 'found buff)))
	      (buffer-list))
      nil)))



(defun imps-assistant-execute-line ()
  (interactive)
  (set-buffer (or (mode-last-visited-buffer 'scheme-mode)
		  (current-buffer)))
  (let* ((beg (progn (beginning-of-line) (point)))
	 (end (progn (forward-sexp) (point)))) ;;used to be  (end-of-line)
    (tea-eval-large-expression-and-update-sqn-and-dg
     (format
      "(execute-command-sequence (sequent-unhash %d) '(%s))"
      (current-sqn-no) (buffer-substring beg end)))
    (forward-line 1)))

;;;(defun imps-assistant-execute-line ()
;;;   (interactive)
;;;   (set-buffer (or (mode-last-visited-buffer 'scheme-mode)
;;;		   (current-buffer)))
;;;   (let* ((beg (progn (beginning-of-line) (point)))
;;;	  (end (progn (forward-sexp) (point))));;used to be  (end-of-line)
;;;     (tea-eval-and-update-sqn-and-dg
;;;      (format
;;;       "(execute-command-sequence (sequent-unhash-in-graph-by-number %d %d) '(%s))"
;;;       (current-sqn-no) dg-number (buffer-substring beg end)))
;;;     (forward-line 1)))


;;;(defun imps-assistant-apply-command ()
;;;  (interactive)
;;;  (let ((command (search-for-completion
;;;		  (read-command-and-advance-point)
;;;		  (imps-command-list))))
;;;    (if (stringp command)
;;;	(progn (message command)
;;;	       (funcall (retrieve-function command) command)))))
;;;
;;;(defun imps-assistant-insert-command ()
;;;  (interactive)
;;;  (let* ((delimiters (command-delimiters))
;;;	 (beg (car delimiters))
;;;	 (end (cdr delimiters))
;;;	 (command (search-for-completion
;;;		   (buffer-substring beg end)
;;;		   (imps-command-list))))
;;;    (if (stringp command)
;;;	(progn (message command)
;;;	       (delete-region beg end)
;;;	       (goto-char beg)
;;;	       (insert command)))))
;;;
;;;(defun read-command-and-advance-point ()
;;;  (let ((delimiters (command-delimiters)))
;;;    (goto-char (cdr delimiters))
;;;    (buffer-substring (car delimiters) (cdr delimiters))))
;;;
;;;(defun command-delimiters ()
;;;  (save-excursion 
;;;    (skip-chars-backward "a-zA-Z0-9-" (point-min))
;;;    (let ((beg (progn (re-search-forward "[^a-zA-Z0-9]*" (point-max) t) (point)))
;;;	  (end (progn (re-search-forward "[a-zA-Z0-9-]*" (point-max) t) (point))))
;;;      (cons beg end))))

(defun imps-insert-current-proof ()
  (interactive)
  (let ((proof (get-literal-from-tea
		"(string-downcase 
                            (with-output-to-string p 
                              (walk 
                                (lambda (x) (newline p) (pretty-print x p))
                              (deduction-graph-readable-history-list (current-dg)))
                              p))")))
    (let ((beg (point)))
      (insert proof)
      (clean-up-proof beg (point))
      (push-mark beg))))

(defun clean-up-proof (beg end)
  (save-excursion
    (goto-char beg)
    (while (search-forward "(block " end t)
      (replace-match "(block 
  "))))

;;;(defun insert-sexp (sexp)
;;;  (cond ((null sexp) (insert "()"))
;;;	((stringp sexp) (insert "\"") (insert sexp) (insert "\""))
;;;	((or (eq sexp 'block) (eq sexp 'script-comment))
;;;	 (insert (downcase (format "%s\n" sexp)))
;;;	 (lisp-indent-line))
;;;	((atom sexp) (insert (downcase (format "%s" sexp))))
;;;	((listp sexp)
;;;	 (insert "(") (insert-sexp (car sexp)) (setq sexp (cdr sexp))
;;;	 (while (and sexp (listp sexp))
;;;	   (insert " ")
;;;	   (insert-sexp (car sexp))
;;;	   (setq sexp (cdr sexp)))
;;;	 (if (null sexp) 
;;;             (insert ")") 
;;;	   (progn
;;;	     (insert " . ")
;;;	     (insert-sexp sexp)
;;;	     (insert ")"))))   
;;;	(t (error "Cannot insert object in buffer."))))

;;;(defun insert-sexp (sexp)
;;;  (cond ((null sexp) (insert "()"))
;;;	((stringp sexp) (insert "\"") (insert sexp) (insert "\""))
;;;	((atom sexp) (insert (downcase (format "%s" sexp))))
;;;	((proper-list-p sexp) (insert "(")
;;;	 (insert-sexp (car sexp))
;;;	 (setq sexp (cdr sexp))
;;;	 (while sexp
;;;	   (insert " ")
;;;	   (insert-sexp (car sexp))
;;;	   (setq sexp (cdr sexp)))
;;;	 (insert ")"))
;;;	((listp sexp)
;;;	 (insert "(") (insert-sexp (car sexp)) (setq sexp (cdr sexp))
;;;	 (while (listp sexp)
;;;	   (insert " ")
;;;	   (insert-sexp (car sexp))
;;;	   (setq sexp (cdr sexp)))
;;;	 (insert " . ")
;;;	 (insert-sexp sexp)
;;;	 (insert ")"))	   
;;;	(t (error "Cannot insert object in buffer."))))

(defun proper-list-p (lst)
  (or (null lst)
      (and (listp lst)
	   (proper-list-p (cdr lst)))))


(defvar autoblock-scripts 't)

(defun turn-on-script-autoblocking ()
  "Turn on automatic insertion of blocks when transcribing proofs."
  (interactive)
  (tea-eval-expression "(turn-on-auto-block)")
  (setq autoblock-scripts 't))


(defun turn-off-script-autoblocking ()
  "Turn off automatic insertion of blocks when transcribing proofs."
  (interactive)
  (tea-eval-expression "(turn-off-auto-block)")
  (setq autoblock-scripts nil))

(defun imps-run-current-proof-script ()
  (interactive)


  (set-buffer (or (mode-last-visited-buffer 'scheme-mode)
		  (current-buffer)))
  (save-excursion
    (end-of-line)
    (re-search-backward df-regexp)
    (re-search-forward "^[ ]*(proof[ \t\n]*(")
    (let ((beg (point)))
      (backward-char 1)
      (forward-sexp 1)
      (backward-char 1)
      (let ((end (point)))
	(tea-eval-large-expression-and-update-sqn-and-dg
	 (format "(execute-command-sequence (sequent-unhash %d) '(%s))"
		 (current-sqn-no) (buffer-substring-if-balanced-defun beg end)))))))

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    
