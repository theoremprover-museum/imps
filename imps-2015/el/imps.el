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

(and window-system			; (v19p)
     ;; The font lock mode may not exist, in older versions of Emacs 19, so
     ;; don't complain if it doesn't exist.
     ;; 
     (load "font-lock"  'noerror 'nomessage)
     (load "imps-font-lock" 'noerror 'nomessage)
     (if (and (boundp '*not-calling-from-emacs*)
	      *not-calling-from-emacs*)
	 (let ((filename  "imps-emacs"))
	   (condition-case var
	       (load filename t t)
	     (error 
	      (message 
	       (mapconcat 
		(function (lambda (x) (format "%s" x)))
		(cdr var)
		" ")))))
;;;Added by jt May-7-2012

       (progn
	 (defun imps-home ()
	   (interactive)
	   (switch-to-buffer (get-buffer-create "IMPS")))

	 (defun imps-tea ()
	   (interactive)
	   (switch-to-buffer (get-buffer-create "*tea*")))

	 (defun imps-sqn ()
	   (interactive)
	   (let ((buff (get-buffer "*Sequent-nodes*")))
	     (if buff (switch-to-buffer  buff)
	       (message "No *Sequent-nodes* buffer currently active"))))

	 )))

(autoload 'imps-reset-current-directory "load-imps-file"
  "Reset the default directory for loading imps files.
Value must always be a shell variable (sans $)."
  't)

(autoload 'imps-load-file "load-imps-file"
  "Load a theory file into Imps.  
Names of theorems, defns, etc are added for completion.  
Optional argument reload if true (prefix arg interactively) means reload 
even if already loaded."
  't)

(defun imps-reload-imps-files ()
  (mapcar
   (function (lambda (sym)
	       (load-library (symbol-name sym))))
   imps-files))
  
(defvar imps-xview-process '())

(defun imps-xview-maybe-start-xdvi ()
  (or (and (processp imps-xview-process)
	   (eq 'run (process-status imps-xview-process)))
      (imps-xview-start-xdvi)))      

(defun imps-xview-start-xdvi ()
  "Start up xdvi, using correct display.  
Modifies IMPS variable PREVIEWER-COMMAND."
  (interactive)
  (let ((default-directory (imps-tmp-dir)))
    (or (file-exists-p (format "%s%s-imps.dvi" default-directory (user-login-name)))
	(copy-file (in-vicinity imps-source-files "../etc/null-imps.dvi")
		   (format "%s%s-imps.dvi" default-directory (user-login-name))))
;;;    (tea-eval-expression
;;;     "(block (set previewer-command \"echo\") repl-wont-print)")
    (setq imps-xview-process
	  (start-process "imps-xtex" nil "xdvi" "-iconic" "-keep"
			 "-s" "4"  "-geometry" "652x704+10+10"
			 (concat (user-login-name) "-imps.dvi")))))

(defun imps-tmp-dir ()
  "This returns the temporary directory for IMPS. Currently it is always /tmp"
  "/tmp/")
;;;(defun imps-tmp-dir ()
;;;  "Expand $IMPS_TMP if that's defined, otherwise /tmp/"
;;;  (let ((imps-dir (getenv "IMPS_TMP")))
;;;    (if imps-dir
;;;	(format "%s/" (expand-file-name imps-dir))
;;;      "/tmp/")))

(defun run-latex-for-imps ()
  (let ((default-directory (imps-tmp-dir)))
    (condition-case var
	(progn (call-process
		"latex" nil 
		(get-buffer-create "*IMPS LaTeX Output*")
		nil
		(concat (user-login-name) "-imps"))
	       (message "Starting xview... done"))
      (error
       (message "Latex failed. Please see system guru.")))))

(defun imps-ref ()
  "Insert (imps-ref ) and poise cursor before left-paren."
  (interactive)
  (insert-string "(imps-ref )")
  (backward-char 1))

(defun imps-set-current-theory (arg)
  (interactive "P")
  (let ((theories
	 (sort
	  (get-literal-from-tea 
	   "(theory-names-in-global-theory-table)")
	  'string-lessp)))
    (let ((string (or arg (imps-completing-read "Theory:" (mapcar 'list theories) nil nil nil)))      )
      (if string (tea-eval-expression
		  (format "(set (current-theory) (name->theory '%s))" string))
	nil))))

;;(fset 'imps-set-current-theory 'set-current-theory)

;;;(defun imps-set-current-theory (theory-name)
;;;  (interactive
;;;   (list  (imps-completing-read "New theory: "
;;;				 imps-obarray
;;;				 'kind-is-theory-p
;;;				 nil
;;;				 nil)))
;;;  (tea-eval-expression (format "(set (current-theory) (name->theory '%s))" theory-name)))
;;;

(defun imps-error (format-string)
  (ding)
  (or (buffer-visible-p (get-buffer "*tea*"))
      (with-output-to-temp-buffer
	    "*IMPS Notification Buffer*"	
	(princ format-string))))

(defvar tea-gc-now nil
  "True of false depending on whether Tea is now garbage collecting now.")

(defun tea-start-gc ()
  (setq tea-gc-now t)
  (message "Tea starting to GC... "))

(defun tea-finish-gc ()
  (setq tea-gc-now nil)
  (message "Tea starting to GC... GC done."))

(define-key inferior-tea-mode-map "\C-co"	'imps-ref)

(defun imps-print-tex-output ()
  (interactive)
  (shell-command
   (format "dvips /tmp/%s-imps | lpr %s"
	   (user-login-name)
	   (mapconcat (function (lambda (a) a))
		      lpr-switches
		      " "))))

(defvar imps-save-tex-dir
  (let ((dir (expand-file-name "~/imps/proofs/")))
    (if (file-directory-p dir)
	dir
      (expand-file-name "~/"))))

(defun imps-save-tex-output ()
  "Copy /tmp/{$USER}-imps.tex to FILENAME." 
  (interactive)
  (let ((filename (read-file-name "Copy to file: " imps-save-tex-dir)))
    (copy-file (format "/tmp/%s-imps.tex" (user-login-name))
	       filename 0 t)))



(defvar imps-input-history '()
  "List of previously submitted IMPS inputs.")

(defconst imps-input-history-max 32
  "Maximum length of imps-input-history ring before oldest elements are thrown away.")

(defvar imps-input-history-offset 0
  "Offset of current entry within imps-input-history")


(defun imps-get-input ()
  (nth imps-input-history-offset imps-input-history))

(defun imps-push-input (str)
  (setq imps-input-history (cons str imps-input-history))
  (if (> (length imps-input-history) imps-input-history-max)
      (setcdr (nthcdr (1- imps-input-history-max) imps-input-history) nil)))

(defun imps-increment-history-offset ()
  (if (< (1+ imps-input-history-offset)
	 (length imps-input-history))
      (setq imps-input-history-offset (1+ imps-input-history-offset))))

(defun imps-decrement-history-offset ()
  (if (< 0 imps-input-history-offset)
      (setq imps-input-history-offset (1- imps-input-history-offset))))

(defun imps-reset-history-offset ()
  (setq imps-input-history-offset 0))

(defun imps-mb-insert-previous-input ()
  (interactive)
  (erase-buffer)
  (insert (imps-get-input))
  (imps-increment-history-offset))
  
(defun imps-mb-insert-next-input ()
  (interactive)
  (erase-buffer)
  (insert (imps-get-input))
  (imps-decrement-history-offset))
  
(defun imps-mb-return ()
  (interactive)
  (imps-reset-history-offset)
  (let ((str (buffer-string)))
    (or (string= str "")
	(imps-push-input str)))
  (exit-minibuffer))

(defun imps-read-from-minibuffer (prompt &optional initial-input keymap read)
  (catch 'minibuffer-read-tag
    ;; I'm sorry if catches and throws are offensive to people, but it
    ;; is very convenient in this case.
    (let ((keymap (or keymap imps-minibuffer-map)))
      (read-from-minibuffer prompt initial-input keymap read))))

;(defun imps-read-from-minibuffer (prompt &optional initial-input keymap read)
;  (let ((keymap (or keymap imps-minibuffer-map)))
;    (read-from-minibuffer prompt initial-input keymap read)))

(defun imps-completing-read (prompt table &optional predicate require-match initial-input)
  (let ((minibuffer-local-completion-map imps-minibuffer-completion-map))
    (completing-read prompt table predicate require-match initial-input)))


(defun abort-resetting-history-offset ()
  "command to abort recursive-edit, resetting imps history offset."
  (interactive)
  (imps-reset-history-offset)
  (abort-recursive-edit))

(defvar inferior-tea-minibuffer-map (copy-keymap inferior-tea-mode-map))
(define-key inferior-tea-minibuffer-map "\C-co" 'imps-ref)
(define-key inferior-tea-minibuffer-map "\C-m" 'imps-mb-return)
(define-key inferior-tea-minibuffer-map "\C-g" 'abort-resetting-history-offset)
(define-key inferior-tea-minibuffer-map "\en" 'imps-mb-insert-next-input)
(define-key inferior-tea-minibuffer-map "\ep" 'imps-mb-insert-previous-input)

(defvar imps-minibuffer-map (copy-keymap minibuffer-local-map))
(define-key imps-minibuffer-map "\C-co" 'imps-ref)
(define-key imps-minibuffer-map "\C-m" 'imps-mb-return)
(define-key imps-minibuffer-map "\C-g" 'abort-resetting-history-offset)
(define-key imps-minibuffer-map "\en" 'imps-mb-insert-next-input)
(define-key imps-minibuffer-map "\ep" 'imps-mb-insert-previous-input)

(defvar imps-minibuffer-completion-map (copy-keymap minibuffer-local-completion-map))
(define-key imps-minibuffer-completion-map "\C-co" 'imps-ref)
(define-key imps-minibuffer-completion-map "\C-m" 'imps-mb-return)
(define-key imps-minibuffer-completion-map "\C-g" 'abort-resetting-history-offset)
(define-key imps-minibuffer-completion-map "\en" 'imps-mb-insert-next-input)
(define-key imps-minibuffer-completion-map "\ep" 'imps-mb-insert-previous-input)


;; (define-key minibuffer-local-map "\en" 'next-history-element)
;; (define-key minibuffer-local-map "\ep" 'previous-history-element)
(define-key minibuffer-local-map "\C-g" 'abort-resetting-history-offset)
(define-key macete-minibuffer-map "\en" 'imps-mb-insert-next-input)
(define-key macete-minibuffer-map "\ep" 'imps-mb-insert-previous-input)
(define-key macete-minibuffer-map "\C-g" 'abort-resetting-history-offset)
(define-key macete-minibuffer-map "\C-m" 'imps-mb-return)


(provide 'imps)

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    
