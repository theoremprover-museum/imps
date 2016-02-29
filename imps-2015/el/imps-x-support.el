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


;; Support for x-mouse and x-menus.
(provide 'imps-x-support)

(defconst no-key "\e[ ")
(defconst l1-key "\e[192z")
(defconst l2-key "\e[193z")
(defconst l3-key "\e[194z")
(defconst l4-key "\e[195z")
(defconst l5-key "\e[196z")
(defconst l6-key "\e[197z")
(defconst l7-key "\e[198z")
(defconst l8-key "\e[199z")
(defconst l9-key "\e[200z")
(defconst l10-key "\e[201z")

(defconst r1-key "\e[208z")
(defconst r2-key "\e[209z")
(defconst r3-key "\e[210z")
(defconst r4-key "\e[211z")
(defconst r5-key "\e[212z")
(defconst r6-key "\e[213z")
(defconst r7-key "\e[214z")
(defconst r9-key "\e[216z")
(defconst r11-key "\e[218z")
(defconst r13-key "\e[220z")
(defconst r15-key "\e[222z")
(defconst alt-key "\e[223z")


(defconst f1-key "\e[224z")
(defconst f2-key "\e[225z")
(defconst f3-key "\e[226z")
(defconst f4-key "\e[227z")
(defconst f5-key "\e[228z")
(defconst f6-key "\e[229z")
(defconst f7-key "\e[230z")
(defconst f8-key "\e[231z")
(defconst f9-key "\e[232z")


(defconst imps-exercise-directory (in-vicinity imps-source-files "../exercises"))

(defun define-keypad-key-softly (map key def)
  "In MAP, cause the string KEY to be bound to DEF."
  (let ((look (lookup-key map key)))
    (cond ((numberp look)
	   (let ((len (1- (length key)))
		 (submap (lookup-key map (substring key 0 (1- look)))))
	     (while (<= look len)
	       (let ((new (make-sparse-keymap)))
		 (define-key submap (char-to-string (aref key (1- look))) new)
		 (setq submap new)
		 (setq look (1+ look))))
	     (define-key map key def)))
	  ((null look)
	   (define-key map key def))
	  (t t))))

(defun ignore-key () "Do nothing interactively" (interactive))

(mapcar
 (function
  (lambda (key)
    (define-keypad-key-softly global-map key 'ignore-key)))
 (list l1-key l2-key l3-key l4-key 
       l5-key l6-key l7-key l8-key 
       l9-key l10-key r1-key r2-key 
       r3-key r4-key r5-key r6-key 
       r7-key r9-key r11-key r13-key
       r15-key alt-key f1-key f2-key
       f3-key f4-key f5-key f6-key
       f7-key f8-key f9-key))

(define-key global-map f1-key 'display-imps-menu)
(define-key global-map f2-key 'imps-x-buffer-menu)
(define-key global-map f3-key 'imps-x-command-menu)
(define-key global-map f4-key 'imps-x-macete-menu)
(define-key global-map f5-key '(lambda () (interactive) (let ((imps-mouse-call-p t)) (set-current-theory nil))))
(define-key global-map f6-key 'insert-template)

(defun imps-popup-menu (arg menu-specs)
  (x-popup-menu arg 
		(cons (car menu-specs) 
		      (cons (let ((x (car (cdr menu-specs))))
			      (cons (car x) (append (cdr x) (list '("CANCEL MENU REQUEST" . nil)))))
			    (cdr (cdr menu-specs))))))

;;;(defconst buffer-panes
;;;  '(("Emacs Buffers"
;;;     ("x-buffer menu (F2)" . imps-x-buffer-menu)
;;;     ("split window vertically (C-x 2)" . split-window-vertically)
;;;     ("delete other windows (C-x 1)" . delete-other-windows)
;;;     ("scroll up (M-v)" . scroll-up)
;;;     ("scroll down (C-v)" . scroll-down))))

;;;(defconst imps-expression-edit-panes
;;;  '(("Build and Edit Expressions"
;;;     ("expression-edit-finished (C-c C-c)" . expression-edit-finished)
;;;     ("expression-xview" . expression-xview))))

(defconst imps-fundamental-panes
  '(("IMPS Help"
     ("IMPS manual entry" . imps-manual-entry)
     ("Find def-form (C-c .)" . imps-find-definition)
     ("Check expression syntax" . check-imps-syntax-of-expression)
     ("Exercises" . imps-exercises)
     ("Insert Proof of Next Theorem" . locate-and-insert-proof)
     ("Current exercise, next problem" . imps-exercise-next-target)
     ("Next Micro Exercise" . imps-next-micro-exercise)
     ("Previous Micro Exercise" . imps-previous-micro-exercise)
     ("Restart Micro Exercise" . imps-repeat-micro-exercise))
    ("Files"
     ("Load file (C-c l)" . tea-load-file)
     ("Find file (C-x C-f)" . find-file)
     ("IMPS file menu" . imps-file-menu))
    ("General"
     ("Set current theory (F5)" . set-current-theory)
     ("Load section" . imps-load-section)
     ("Load references for section" . imps-load-section-references)
     ("Quick-load section" . imps-quick-load-section)
     ("Theory network status" . imps-status)
     ("Examine command history" . examine-command-history)
;;     ("Examine theory interpretation" . examine-theory-interpretation)
     ("Reset dump" . imps-reset-dump)
     ("Interrupt IMPS" . interrupt-tea-process)
     ("Continue IMPS" . continue-tea-process)
     ("Run IMPS" . run-imps)
     ("Quit IMPS" . quit-imps))))

(defconst imps-proof-panes 
  '(("Deduction Graphs"
     ("Display dg chunk (.)" . sqn-display-dg-chunk)
     ("Read and start dg" . imps-read-and-start-deduction)
     ("Save dg script" . imps-save-history)
     ("Start dg" . imps-start-deduction)
     ("Update dg display" . dg-update-sqn-and-dg)
     ("Verbosely update dg display" . (lambda (arg) (dg-update-sqn-and-dg t)))
     ("Run dg history" . imps-run-proof))))

(defconst error-panes
  '((""
     ("Delete error window" . delete-error-window)
     ("Examine command history" . examine-command-history))))

(defconst starting
  '(("Starting IMPS"
     ("Run IMPS" . run-imps))))

(defconst stopping
  '(("Stopping IMPS"
     ("Quit IMPS" . quit-imps))))

(defconst scheme-mode-panes
  '(("Building IMPS Objects"
     ("Evaluate def-form (C-c e)" . tea-send-definition)
     ("Evaluate def-form; go to tea (C-c C-e)" . tea-send-definition-and-go)
     ("Insert def-form template (F6)" . insert-template))
    ("Editing and Executing Proof Scripts"
     ("Insert proof script (C-c i)" . imps-insert-current-proof)
     ("Execute proof line (C-c l)" . imps-assistant-execute-line)
     ("Execute region (C-c r)" . imps-assistant-execute-region))))

(defconst imps-dg-panes
  '(("Extending the Deduction Graph"
     ("Command menu (F3 or ?)" . imps-x-command-menu)
     ("Special command menu" . imps-x-special-command-menu)
     
     ("Macete menu (F4)" . imps-x-macete-menu)
     ("Macete description buffer (C-c ?)" . imps-macete-menu)
     ("Comment preceding entry" .  imps-comment-latest-entry))
    ("Changing Sequent Nodes"
     ("First unsupported relative (F)" . imps-first-unsupported-relative)
     ("First unsupported descendent " . imps-first-unsupported-descendent)
     ("Sqn by number" . sqn-select)
     ("Maximum sqn" . sqn-display-max)
     ("Next sqn (n)" . sqn-display-next)
     ("Previous sqn (p)" . sqn-display-previous)
     ("Parent (P)" . imps-parent)
     ("First child (C)" . imps-first-child)
     ("Next sibling (S)" . imps-next-sibling))
    ("Viewing Objects with TeX"
     ("Xview sqn (x)" . sqn-xview)
     ("Xview dg (X)" . dg-xview-dg)
     ("Xview thm" . imps-xview-theorem))))


(defvar imps-mouse-call-p '())

(defun display-imps-menu (arg)
  (interactive "P")
  (let ((imps-mouse-call-p t))
    
    
    (let ((selection
	   (if (buffer-visible-p "*IMPS Notification Buffer*")
	       (imps-popup-menu
		arg
		(cons "Error Menu" error-panes))
	     (imps-popup-menu
	      arg
	      (cons "Menu"
		    (append
		     imps-dg-panes
		     imps-proof-panes
		     imps-fundamental-panes
		     scheme-mode-panes))))))
      
      (and selection (if (commandp selection)
			 (call-interactively selection)
		       (funcall selection arg))))))

(defconst *command-key-binding-alist*
  '(("simplify" . " (C-c s)")
    ("beta-reduce-repeatedly" . " (C-c b)")
    ("backchain" . " (b)")
    ("induction" . " (i)")
    ("extensionality" . " (~)")
    ("direct-and-antecedent-inference-strategy" . " (D)")
    ("direct-inference" . " (d)")
    ("force-substitution" . " (f)")
    ("raise-conditional" . " (r)")
    ("unfold-single-defined-constant" . " (u)")
    ("unfold-single-defined-constant-globally" . " (U)")
    ("unfold-defined-constants" . " (C-c U)")
    ("antecedent-inference" . " (a)")
    ("contrapose" . " (c)")
    ("weaken" . " (w)")
    ("incorporate-antecedent" . " (@)")))


(defun command-with-key-binding (command)
  (let ((key (cdr (assoc command *command-key-binding-alist*))))
    (if key (concat command key) command)))

(defun imps-x-command-menu (arg)
  (interactive "P")
  (let ((sqn-no (current-sqn-no))
	(imps-mouse-call-p t))
    (message "Updating Command Menu...")
    (let ((commands 
	   (get-literal-from-tea 
	    (format "(applicable-commands (sequent-unhash %d))" sqn-no))))
      
      (message "Done.")
      (let ((string (imps-popup-menu
		     '(0 0)
		     (list "Command Menu"
			   (cons "Commands"
				 (mapcar
				  '(lambda (x)
				     (cons (command-with-key-binding x) x))
				  commands))))))
	
	(if string (eval (car (read-from-string (format "(dg-apply-command \"%s\" '(%d))"
							string
							sqn-no)))))))))								      
(defun imps-x-special-command-menu (arg)
  (interactive "P")
  (let ((sqn-no (current-sqn-no))
	(imps-mouse-call-p t))
    (message "Updating Special Command Menu...")
    (let ((commands 
	   (get-literal-from-tea 
	    (format "(applicable-special-commands (sequent-unhash %d))" sqn-no))))
      (message "Done.")
      (let ((string (imps-popup-menu
		     '(0 0)
		     (list "Special Command Menu"
			   (cons "Commands"
				 (mapcar
				  '(lambda (x)
				     (cons (command-with-key-binding x) x))
				  (append 
				   (list "apply-macete (without-minor-premises)"
					 "apply-macete-locally"
					 "apply-macete-locally-with-minor-premises"
					 "apply-macete-with-minor-premises")
				   commands)))))))
	
	(if string 
	    (cond ((string-equal string "apply-macete (without-minor-premises)")
		   (apply-macete-menu arg))
		  ((string-equal string "apply-macete-locally")
		   (apply-macete-locally-menu arg))
		  ((string-equal string "apply-macete-locally-with-minor-premises")
		   (apply-macete-locally-with-minor-premises-menu arg))
		  ((string-equal string "apply-with-minor-premises-macete")
		   (apply-macete-with-minor-premises-menu arg))
		  (t
		   (eval (car (read-from-string (format "(dg-apply-command \"%s\" '(%d))"
							string
							sqn-no)))))))))))							      

(defun imps-x-macete-menu (arg)
  (interactive "P")
  (imps-x-macete-menu-aux "apply-macete-with-minor-premises"))

(defun apply-macete-menu (arg)
  (interactive "P")
  (imps-x-macete-menu-aux "apply-macete"))

(defun apply-macete-with-minor-premises-menu (arg)
  (interactive "P")
  (imps-x-macete-menu-aux "apply-macete-with-minor-premises"))

(defun apply-macete-locally-menu (arg)
  (interactive "P")
  (imps-x-macete-menu-aux "apply-macete-locally"))

(defun apply-macete-locally-with-minor-premises-menu (arg)
  (interactive "P")
  (imps-x-macete-menu-aux "apply-macete-locally-with-minor-premises"))

(defun imps-x-macete-menu-aux (macete-command)
  (let ((sqn-no (current-sqn-no))
	(imps-mouse-call-p t))
    (message "Updating Macete Menu...")
    (let ((macetes 
	   (sort
	    (get-literal-from-tea 
	    (format "(applicable-macetes-for-sqn (sequent-unhash %d))" sqn-no))
	    'string-lessp)))
      
      (message "Done.")
      (if macetes
	  (let ((string (imps-popup-menu
			 '(0 0)
			 (list "macete-menu"
			       (cons "Macete Menu"
				     (mapcar
				      '(lambda (x)
					 (cons x x))
				      macetes))))))
	    
	    (if string
		(let ((*macete-from-menu*
		       (car (read-from-string string))))
		  (dg-apply-command macete-command (list sqn-no)))

	      nil))
	(message "No applicable macetes!")))))

(defun imps-x-buffer-menu (arg)
  "Pop up a menu of IMPS buffers for selection with the mouse."
  (interactive "P")
  (let ((menu
	 (list "Buffer Menu"
	       (cons "IMPS Buffers"
		     (let ((tail (buffer-list))
			   head
			   dot-tea)
		       (while tail
			 (let ((elt (car tail)))
			   (if (string-match
				"^\\*Deduction\\|^\\*Sequent-nodes\\|^\\*tea\\*$"
					     (buffer-name elt))
			       (setq head (cons
					   (cons
					    (format
					     "%s"
					     (buffer-name elt))
					    elt)
					   head))
			     (if (string-match "\\.t$" (buffer-name elt))
				 (setq dot-tea (cons
						(cons
						 (format
						  "%s"
						  (buffer-name elt))
						 elt)
						dot-tea))))
			   
			   
			   (setq tail (cdr tail))))
		       (append head dot-tea))))))
    (switch-to-buffer (or (imps-popup-menu arg menu) (current-buffer)))))


(defun imps-file-menu (arg)
  (interactive "P")
  (file-menu (in-vicinity imps-source-files "")))

(defun file-menu (directory)
  (let ((all-files (directory-files directory))
	(files-with-attributes '()))
    (mapcar '(lambda (x)
	       (let* ((full-x (concat directory "/" x))
		      (attributes (file-attributes full-x)))
		 (if (car attributes);;directory?
		     (setq files-with-attributes
			   (cons (list x full-x attributes)
				 files-with-attributes))
		   (if (string-match "\\.t$\\|\\.el$\\|\\.tex$" x)
		       (setq files-with-attributes
			     (cons (list x full-x attributes)
				   files-with-attributes))))))
	    all-files)
    (let ((selection
	   (imps-popup-menu '()
			 (list "Directory"
			       (cons (concat "-" directory "-") files-with-attributes)))))
      (if (car (nth 1 selection))
	  (file-menu (nth 0 selection))
	(find-file (nth 0 selection))))))


(defun imps-reset-dump (arg)
  (let ((in-dump-dir (directory-files (in-vicinity imps-source-files "../executables") t))
	(file-menu-spec '()))
    (mapcar '(lambda (x) (if (null (car (file-attributes x)))
			     (setq file-menu-spec (cons (cons x x) file-menu-spec))))
	    in-dump-dir)
    (let ((selection
	   (imps-popup-menu '()
			 (list "Dumps"
			       (cons "-dumps-"
				     file-menu-spec)))))
      (setq imps-dump-name selection))))


(defun examine-command-history (arg)
  (interactive "P")
  (switch-to-buffer " *Tea script*")
  (goto-char (point-max))
  (backward-sexp))


;;;(defun examine-theory-interpretation (arg)
;;;  (interactive  "P")
;;;  (let ((translations
;;;	 (get-literal-from-tea
;;;	  "(let ((accum '()))
;;;               (walk (lambda (x) (if (name x) 
;;;                                     (push accum (list (string-downcase (symbol->string (name x)))))))
;;;                         (translations-in-global-translation-alist))
;;;             accum)")))
;;;    (examine-imps-object "translation" (completing-read-or-get-from-x-menu "Interpretations: " translations nil nil nil))))

;;;(defun examine-imps-object (type name)
;;;  (tea-eval-expression
;;;   (format "(block
;;;             (pretty-print (name->%s '%s) (standard-output))
;;;             (newline (standard-output))
;;;             (pretty-print (let* ((obj (name->%s '%s)))
;;;                (map (lambda (sel) (list (selector-id sel) (sel obj))) (stype-selectors (structure-type obj)))) (standard-output)))"
;;;	   type name type name))
;;;  (pop-to-buffer "*tea*"))

;; (autoload 'imps-tutorial-formulas
;; 	  (concat (getenv "IMPS") "/../el/imps-tutorial")
;; 	  "Starts the IMPS interactive tutorial"
;; 	  t)


(defun imps-exercises (arg)
  (require 'imps-tutorial)
  (let ((all-files (nreverse (sort (directory-files imps-exercise-directory) 'string-lessp)))
	(files '()))
    (mapcar '(lambda (x)
	       (if (string-match "\\.t$\\|\\.el$\\|\\.tex$" x)
		   (let ((y (substring x 0 (match-beginning 0))))
		     (setq files
			   (cons (list y (concat imps-exercise-directory "/" x) x) files)))))
	    all-files)
    (let ((selection
	   (imps-popup-menu arg
			 (list "Directory"
			       (cons "-*-" files)))))
      (if selection
	  (let ((filename (concat "~/imps/theories/" (nth 1 selection))))
	    (copy-file (nth 0 selection) filename 1)
	    (find-file filename)
	    (delete-all-exercise-proofs)
	    (save-buffer)
	    (set-marker imps-exercise-already-sent-marker (point-min))
	    (imps-exercise-next-target))))))

(defun set-current-theory (arg)
  (interactive "P")
  (let ((theories
	 (sort
	  (get-literal-from-tea 
	   "(theory-names-in-global-theory-table)")
	  'string-lessp)))
    (let ((string (or arg (completing-read-or-get-from-x-menu "Theory:" (mapcar 'list theories) nil nil nil)))      )
      (if string (tea-eval-expression
		  (format "(set (current-theory) (name->theory '%s))" string))
	nil))))

(defun imps-load-section (arg)
  (interactive "P")
  (let ((sections
	 (sort
	  (get-literal-from-tea 
	   "(let ((accum `())) (walk-table (lambda (k v) (push accum (string-downcase (symbol->string (section-name v))))) *name-section-table*) accum)")
	  'string-lessp)))

    (let ((string (completing-read-or-get-from-x-menu "section:" (mapcar 'list sections) nil nil nil)))      
      (if string (tea-eval-expression
		  (format "(load-section %s)" string))
	nil))))

(defun imps-quick-load-section (arg)
  (interactive "P")
  (let ((sections
	 (sort
	  (get-literal-from-tea 
	   "(let ((accum `())) (walk-table (lambda (k v) (push accum (string-downcase (symbol->string (section-name v))))) *name-section-table*) accum)")
	  'string-lessp)))

    (let ((string (completing-read-or-get-from-x-menu "section:" (mapcar 'list sections) nil nil nil)))      
      (if string (tea-eval-expression
		  (format "(load-section %s quick-load)" string))
	nil))))

(defun imps-load-section-references (arg)
  (interactive "P")
  (let ((sections
	 (sort
	  (get-literal-from-tea 
	   "(let ((accum `())) (walk-table (lambda (k v) (push accum (string-downcase (symbol->string (section-name v))))) *name-section-table*) accum)")
	  'string-lessp)))
    (let ((string
	   (completing-read-or-get-from-x-menu
	    "section: "
	    (mapcar 'list sections)
	    nil nil nil)))      
      (and
       string
       (tea-eval-expression
	(format "(emacs-install-section-references '%s)" string))))))


;;;(defun set-current-theory (arg)
;;;  (interactive "P")
;;;  (let ((theories
;;;	 (sort
;;;	  (get-literal-from-tea 
;;;	   "(theory-names-in-global-theory-alist)")
;;;	  'string-lessp)))
;;;    (let ((string (imps-popup-menu
;;;		   '(0 0)
;;;		   (list "Theory Menu"
;;;			 (cons "Theories"
;;;			       (mapcar
;;;				'(lambda (x)
;;;				   (cons x x))
;;;				theories))))))
;;;      
;;;      (if string (tea-eval-expression
;;;		  (format "(set (current-theory) (name->theory '%s))" string))
;;;	nil))))

(defun imps-status (arg)
  (interactive "P")
  (let ((stat (get-literal-from-tea "(status-of-theory-network-alist)")))
    (message (mapconcat '(lambda (x) (concat (symbol-name (car x)) "=" (cdr x)))  stat " "))))


(defun delete-error-window (arg)
  (interactive "P")
  (tea-eval-expression "(reset)")
  (replace-buffer-in-windows "*IMPS Notification Buffer*"))


(defun replace-chars-in-string (str from-char to-char)
  (let* ((str (copy-sequence str))
	 (len (length str))
	 (m 0))
    (while (< m len)
      (if (char-equal (aref str m) from-char)
	  (aset str m to-char))
      (setq m (+ 1 m)))
    str))


;;;Additional mouse support for IMPS.

(defun mode-line-selected-window-p (arg &optional any)
  "Returns t if the mouse ARG is pointing to a modeline; 
   if optional ANY is non-nil, modeline of the selected window."
  (let ((start-w (selected-window))
	(done nil)
	(w (selected-window))
	(selected nil)
	(modeline-window nil))
    (while (not (or done (setq selected (coordinates-in-window-p arg w))))
      (setq w (next-window w t))
      
      ;;This is a hyperhack!
      ;;Picks out the window the modeline is pointing to.
      
      (if (= (nth 3 (window-edges w)) (1+ (car (cdr arg))))
	  (setq modeline-window w))
      
      (if (eq w start-w)
	  (setq done t)))
    (and (not selected)
	 (or any
	     (not modeline-window)
	     (set-buffer (window-buffer modeline-window))))))

;;;(= (nth 3 (window-edges start-w)) (1+ (car (cdr arg))))
;;;(error "Mouse not on mode line of selected buffer.")

;;;(defun x-mouse-window (arg)
;;;  "Returns emacs window the mouse is on or nil if mouse is not in a buffer window"
;;;  (let ((start-w (selected-window))
;;;	(done nil)
;;;	(w (selected-window))
;;;	(selected nil))
;;;    (while (not (or done (setq selected (coordinates-in-window-p arg w))))
;;;      (setq w (next-window w t))
;;;      (if (eq w start-w)
;;;	  (setq done t)))
;;;    (if selected w nil)))

;;starting up the menus just by mouse clicks

;;;(setq-default x-process-mouse-hook 
;;;	      '(lambda (arg key)
;;;		 (save-window-excursion
;;;		   (if (mode-line-selected-window-p arg)
;;;		       (if (<= (car arg) 12)
;;;			   (cond ((and (<= (car arg) 5) (= key 0))
;;;				  (message "")
;;;				  (scroll-down))
;;;				 ((and (< 6 (car arg)) (<= (car arg) 12) (= key 0))
;;;				  (message "")
;;;				  (scroll-up)))
;;;			 (cond ((= key 0);;x-button-right
;;;				(message "Release button for IMPS menu."))
;;;			       ((= key 4);;x-button-right-up.
;;;				(message "")
;;;(display-imps-menu arg))))))))

(setq x-process-mouse-hook 
      '(lambda (arg key)
	 (if (mode-line-selected-window-p arg)
	     (cond ((= key 0);;x-button-right
		    (message "Release button for IMPS menu."))
		   ((= key 4);;x-button-right-up.
		    (message "")
		    (display-imps-menu arg))))))

;;We assume formulas are separated by  *formula-terminator-string*:
(defvar *formula-terminator-string* "\n\n")

(defconst assumption-number-mouse-hook
  '(lambda (arg key)
     (cond ((= key 4);;x-button-right-up
	    (let ((numb (mouse-count-occurrences-backwards
			 *formula-terminator-string*
			 assumption-assertion-separator
			 arg)))
	      (if (numberp numb)
		  (insert-in-minibuffer
		   (format "%s " numb)))))
	   ((= key 0)
	    (message "Select antecedent formula with mouse.")))))

(defun insert-in-minibuffer (str &optional erase)
  "Inserts STR in minibuffer."
  (set-buffer (window-buffer (minibuffer-window)))
  (if erase (erase-buffer))
  (insert str))

(defun count-occurrences-backwards (regexp)
  (save-excursion
    (let ((count 0)
	  (beg (point-min)))
      (while (re-search-backward regexp beg t)
	(setq count (1+ count)))
      count)))

(defun mouse-count-occurrences-backwards (terminator boundary arg)
  (save-window-excursion
    (let* ((relative-coordinate (x-mouse-select arg))
	   (rel-x (car relative-coordinate))
	   (rel-y (car (cdr relative-coordinate))))
      (if relative-coordinate
	  (progn
	    (move-to-window-line rel-y)
	    (move-to-column (+ rel-x (current-column)))
	    (if (eq (current-buffer)  (dgr-sqn-buffer))
		(if (or (and (looking-at "[ \t\n]\\|\\'")
			     (save-excursion
			       (skip-chars-backward " \t\n")
			       (looking-at terminator)))
			(save-excursion
			  (beginning-of-line)
			  (looking-at (concat "[ \t]*" boundary "\n\n")))
			(save-excursion
			  (re-search-backward boundary (point-min) t)))
		    (progn
		      (message "Mouse not pointing at assumption.") (ding) nil)
		  (count-occurrences-backwards terminator))
	      (progn (message "Mouse is in wrong buffer!") (ding) nil)))))))


;;;Grabbing expressions with the mouse:

(defconst expression-grabber-mouse-hook
  '(lambda (arg key)
     (cond ((= key 4);;x-button-right-up
	    (let ((expr (mouse-locate-containing-expression arg)))
	      (if expr (insert-in-minibuffer expr t))))
	   ((= key 0)
	    (message "Select formula with mouse and release button.")))))

(defconst left-delimiter-for-imps-expressions "\"")
(defconst right-delimiter-for-imps-expressions "\"")
					;(defconst regexp-for-imps-expressions "\"[^\"]+\"")

(defun locate-containing-expression ()
  (save-excursion
    (let ((beg nil) (end nil))
      (re-search-forward right-delimiter-for-imps-expressions (point-max) t)
      (setq end (point))
      (goto-char (match-beginning 0))
      (if end
	  (progn
	    (re-search-backward left-delimiter-for-imps-expressions (point-min) t)
	    (setq beg (point))
	    (goto-char (match-end 0))
	    (if beg 
		(format "%s" (buffer-substring (1+ beg) (- end 1)))
	      nil))
	nil))))

;;;(defun locate-containing-expression ()
;;;  (save-excursion
;;;    (let ((p (point)))
;;;      (goto-char (point-max))
;;;      (let ((data nil))
;;;	(while (and (re-search-backward regexp-for-imps-expressions (point-min) t)
;;;		    (< p (car (setq data (match-data)))))
;;;	  (re-search-forward left-delimiter-for-imps-expressions (point-max) t))
;;;	(if (and (<= (nth 0 data) p)  (<= p (nth 1 data)))
;;;	    (format "%s" (buffer-substring (nth 0 data) (nth 1 data)))
;;;	  nil)))))

(defun mouse-locate-containing-expression (arg)
  (save-window-excursion
    (let* ((relative-coordinate (x-mouse-select arg))
	   (rel-x (car relative-coordinate))
	   (rel-y (car (cdr relative-coordinate))))
      (if relative-coordinate
	  (progn
	    (move-to-window-line rel-y)
	    (move-to-column (+ rel-x (current-column)))
	    (let ((expr (locate-containing-expression)))
	      (cond ((null expr) (ding) (message "Not pointing to anything which is recognizably an expression.") nil)
		    (t expr))))))))



;;additional hooks:

;;;(setq imps-minibuffer-hook
;;;      (function
;;;       (lambda () (setq mode-line-format (cons " -UP- |-DOWN-| " mode-line-format)))))
;;;
;;;
;;;(defun add-hook (sym add-on)
;;;  (set sym
;;;       (if (boundp sym)
;;;	   (if (listp (symbol-value sym))
;;;	       (if (eq (car (symbol-value sym)) 'lambda)
;;;		   (list (symbol-value sym) add-on)
;;;		 (append (symbol-value sym) (list add-on)))
;;;	     (list (symbol-value sym) add-on))
;;;	 add-on)))
;;;
;;;(add-hook 'scheme-mode-hook imps-minibuffer-hook)
;;;		  
;;;(add-hook 'sqn-mode-hook imps-minibuffer-hook)
;;;
;;;(add-hook 'dg-mode-hook imps-minibuffer-hook)


    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    
