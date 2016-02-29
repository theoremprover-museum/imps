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



(provide 'imps-lucid-support)

(defconst imps-exercise-directory (in-vicinity imps-source-files "../exercises"))

(defvar imps-mouse-call-p '())

(defun set-local-buttons-hook ()
  (local-set-key 'button3 'run-imps-mouse-hooks))

(defun run-imps-mouse-hooks (event)
  (interactive "@e")
  (funcall x-process-mouse-hook event))

(defvar x-process-mouse-hook 'x-mouse-activate-point-to-mouse)

(defun call-or-eval (fn)
  (cond ((commandp fn) (call-interactively fn))
	((symbolp fn) (funcall fn))
	(t (eval fn))))

(defconst *command-key-binding-alist*
  '(("simplify" . "C-c s")
    ("beta-reduce-repeatedly" . "C-c b")
    ("backchain" . "b")
    ("induction" . "i")
    ("extensionality" . "~")
    ("direct-and-antecedent-inference-strategy" . "D")
    ("direct-inference" . "d")
    ("force-substitution" . "f")
    ("raise-conditional" . "r")
    ("unfold-single-defined-constant" . "u")
    ("unfold-single-defined-constant-globally" . "U")
    ("unfold-defined-constants" . "C-c U")
    ("antecedent-inference" . "a")
    ("contrapose" . "c")
    ("weaken" . "w")
    ("incorporate-antecedent" . "@")))

;; (defconst *command-key-binding-alist*
;;   '(("simplify" . " (C-c s)")
;;     ("beta-reduce-repeatedly" . " (C-c b)")
;;     ("backchain" . " (b)")
;;     ("induction" . " (i)")
;;     ("extensionality" . " (~)")
;;     ("direct-and-antecedent-inference-strategy" . " (D)")
;;     ("direct-inference" . " (d)")
;;     ("force-substitution" . " (f)")
;;     ("raise-conditional" . " (r)")
;;     ("unfold-single-defined-constant" . " (u)")
;;     ("unfold-single-defined-constant-globally" . " (U)")
;;     ("unfold-defined-constants" . " (C-c U)")
;;     ("antecedent-inference" . " (a)")
;;     ("contrapose" . " (c)")
;;     ("weaken" . " (w)")
;;    ("incorporate-antecedent" . " (@)")))

(defun command-with-key-binding (command)
  (let ((key (cdr (assoc command *command-key-binding-alist*))))
    (if key (concat command key) command)))

(defun command-key (command)
  (cdr (assoc command *command-key-binding-alist*)))

(defconst imps-proof-panes 
  '(
    ("DG"
     ["Start dg" (call-or-eval 'imps-start-deduction) t]
     ["Update dg display" (call-or-eval' dg-update-sqn-and-dg) t]
     ["Verbosely update dg display" (call-or-eval 'verbosely-dg-update-sqn-and-dg) t]
     ["Jump to dg" (call-or-eval 'sqn-display-dg-chunk) :active (eq major-mode 'sqn-mode) :keys  "."]
     ["Jump to sqn"  (call-or-eval 'dg-display-sqn) :active (eq major-mode 'dg-mode) :keys  "."]
     ["Read and start dg" (call-or-eval 'imps-read-and-start-deduction) t] ))
  )

;(Defun imps-proof-panes ()
;  (let ((basic
;	 '(["Start dg" (call-or-eval 'imps-start-deduction) t]
;;;
;;;  ["Start another dg" (call-or-eval 'imps-new-start-deduction) t]
;;;  
;	   ["Update dg display" (call-or-eval 'dg-update-sqn-and-dg) t]
;	   ["Verbosely update dg display" (call-or-eval '(dg-update-sqn-and-dg t)) t]
    
;    (list (cons "DG"
;		(if (eq major-mode 'sqn-mode)
;		    (append '(["Display dg chunk (.)" (call-or-eval 'sqn-display-dg-chunk) t]
;			      ["Read and start dg" (call-or-eval 'imps-read-and-start-deduction) t])
;			    basic)
;		  (if (eq major-mode 'dg-mode)
;		      (append '(["Display sqn (.)" (call-or-eval 'dg-display-sqn) t])
;			      basic)
;		    basic))))))

(defconst imps-default-menubar
  (nconc default-menubar (list ["IMPS" imps-menu-toggle-menubar t])))

(defconst imps-fundamental-panes
  '(
    ("IMPS-Help"
;;     ["IMPS manual entry"   (call-or-eval 'imps-manual-entry) t]
;;     ["Find def-form" (call-or-eval 'imps-find-definition) :keys "C-c ."]
;;     ["Check expression syntax" (call-or-eval 'check-imps-syntax-of-expression) t]
;;     ["Tutorial" (call-or-eval 'imps-tutorial-formulas) t]
     "--" "Micro Exercises" "--"
     ["Next micro exercise" (call-or-eval 'imps-next-micro-exercise) t]
     ["Previous micro exercise" (call-or-eval 'imps-previous-micro-exercise) t]
     ["Restart micro exercise" (call-or-eval 'imps-repeat-micro-exercise) t]
     "--"
     ["Exercises" (call-or-eval 'imps-exercises) t]
     ["Insert proof of next theorem" (call-or-eval 'locate-and-insert-proof) t]
     ["Current exercise: next problem" (call-or-eval 'imps-exercise-next-target) t]
     ["Restart exercise in current buffer" (call-or-eval 'imps-exercise-start-in-current-file) t]
)
    
    ("General"
     ["Set current theory" (call-or-eval 'set-current-theory) t]
     ["Load IMPS file"  (call-or-eval 'imps-load-file) t]
     ["Load section" (call-or-eval 'imps-load-section) t]
;;     ["Load references for section" (call-or-eval 'imps-load-section-references) t]
     ["Quick-load section" (call-or-eval 'imps-quick-load-section) t]
     "--"
     ["Theory network status" (call-or-eval 'imps-status) t]
;     ["Examine theory interpretation" (call-or-eval 'examine-theory-interpretation) t]
     "--"
;;     ["Reset imps-program" (call-or-eval 'imps-reset-imps-program) t]
;;     ["Interrupt IMPS" (call-or-eval 'interrupt-tea-process) t]
;;     ["Continue IMPS"  (call-or-eval 'continue-tea-process) t]
     ["Run IMPS" (call-or-eval 'run-imps) t]
     ["Quit IMPS" (call-or-eval 'quit-imps) t])))

(defconst scheme-mode-panes
  '(("Def-forms"
     ["Evaluate def-form" (call-or-eval 'tea-send-definition) :keys  "C-c e" :active (eq major-mode 'scheme-mode)]
     ["Evaluate def-form; go to tea" (call-or-eval 'tea-send-definition-and-go) :keys "C-c C-e" :active (eq major-mode 'scheme-mode)]
     ["Insert def-form template" (call-or-eval 'insert-template) :active (eq major-mode 'scheme-mode)]
     "--"
     ["List def-forms" (call-or-eval 'df-list-create-or-restore) t]
     ["Show this listed def-form" (call-or-eval 'df-show-current-def-form) t]
     ["Show next listed def-from" (call-or-eval 'df-show-next-def-form) t]
     ["Show previous listed def-form" (call-or-eval 'df-show-previous-def-form) t]
     ["Evaluate listed def-form" (call-or-eval 'df-evaluate-def-form) t])
    ("Scripts"
     ["Insert proof script" (call-or-eval 'imps-insert-current-proof) :keys "C-c i"]
     "--"
     ["Execute proof line" (call-or-eval 'imps-assistant-execute-line) :keys "C-c l"]
     ["Execute region" (call-or-eval 'imps-assistant-execute-region) :keys "C-c r"]
     ["Execute script of current def-form"  (call-or-eval 'imps-run-current-proof-script) :keys "C-c x"]
     ["Autoblocking on" (call-or-eval 'turn-on-script-autoblocking) t]
     ["Autoblocking off" (call-or-eval 'turn-off-script-autoblocking) t])))

(defconst imps-dg-panes
  '(("Extend-DG"
     ["Commands" (call-or-eval 'imps-x-command-menu) :active (eq major-mode 'sqn-mode) :keys "?"]
     ["Macetes (with minor premises)"
      (call-or-eval 'apply-macete-with-minor-premises-menu) :active (eq major-mode 'sqn-mode)]
     "---"
     ("Annotations"
      ["Comment preceding entry"  (call-or-eval 'imps-comment-latest-entry) :active (eq major-mode 'sqn-mode)]
      ["Annotate" (call-or-eval '(dg-apply-command "annotate" (list (current-sqn-no)))) :active (eq major-mode 'sqn-mode)])
     ("Macetes"

      ["Without minor premises" (call-or-eval 'apply-macete-menu) :active (eq major-mode 'sqn-mode)]
      ["Locally" (call-or-eval 'apply-macete-locally-menu) :active (eq major-mode 'sqn-mode)]
      ["Locally and with minor-premises" (call-or-eval 'apply-macete-locally-with-minor-premises-menu) :active (eq major-mode 'sqn-mode)]

      )
     ["Special commands" (call-or-eval 'imps-x-special-command-menu) :active (eq major-mode 'sqn-mode)]

     ["Macete description" (call-or-eval 'imps-macete-menu ) :active (eq major-mode 'sqn-mode) :keys "C-c ?"])
    ("Nodes"
     ["First unsupported relative" (call-or-eval 'imps-first-unsupported-relative) :active (eq major-mode 'sqn-mode) :keys "F"]
     ["First unsupported descendent" (call-or-eval 'imps-first-unsupported-descendent) :active (eq major-mode 'sqn-mode)]
     ["Sqn by number" (call-or-eval 'sqn-select) :active (eq major-mode 'sqn-mode)]
     ["Maximum sqn" (call-or-eval 'sqn-display-max) :active (eq major-mode 'sqn-mode)]
     ["Next sqn" (call-or-eval 'sqn-display-next) :active (eq major-mode 'sqn-mode) :keys "n" ]
     ["Previous sqn" (call-or-eval 'sqn-display-previous) :active (eq major-mode 'sqn-mode) :keys "p"]
     ["Parent" (call-or-eval 'imps-parent) :active (eq major-mode 'sqn-mode) :keys "P"]
     ["First child" (call-or-eval 'imps-first-child) :active (eq major-mode 'sqn-mode) :keys "C"]
     ["Next sibling" (call-or-eval 'imps-next-sibling ) :active (eq major-mode 'sqn-mode) :keys "S"])
    ("TeX"
     ["Start xdvi" (call-or-eval 'imps-xview-start-xdvi) :active (eq major-mode 'sqn-mode)]
     ["Xview sqn" (call-or-eval 'sqn-xview) :active (eq major-mode 'sqn-mode) :keys "x"]
     ["Xview sqns" (call-or-eval 'imps-xview-sqns) :active (eq major-mode 'sqn-mode)]
     ["Xview dg" (call-or-eval 'dg-xview-dg) :active (eq major-mode 'sqn-mode) :keys "X"]
     ["Xview thm" (call-or-eval 'imps-xview-theorem) :active (eq major-mode 'sqn-mode)]
     ["Xview macete" (call-or-eval 'imps-xview-macete) :active (eq major-mode 'sqn-mode)]
     ["Save last TeX output" (call-or-eval 'imps-save-tex-output) :active (eq major-mode 'sqn-mode)]
     ["Print TeX output" (call-or-eval 'imps-print-tex-output) :active (eq major-mode 'sqn-mode)])))

;;;(defconst imps-dg-panes
;;;  '(("Extend-DG"
;;;     ["command menu (?)" (call-or-eval 'imps-x-command-menu) t]
;;;     ["special command menu" (call-or-eval 'imps-x-special-command-menu) t]
;;;     "---"
;;;     ["macete menu" (call-or-eval 'imps-x-macete-menu) t]
;;;     ["macete description buffer (C-c ?)" (call-or-eval 'imps-macete-menu )t])
;;;    ("Nodes"
;;;     ["first unsupported relative " (call-or-eval 'imps-first-unsupported-relative) t]
;;;     ["first unsupported descendent (F)" (call-or-eval 'imps-first-unsupported-descendent) t]
;;;     ["sqn by number" (call-or-eval 'sqn-select) t]
;;;     ["maximum sqn" (call-or-eval 'sqn-display-max) t]
;;;     ["next sqn (n)" (call-or-eval 'sqn-display-next) t]
;;;     ["previous sqn (p)" (call-or-eval 'sqn-display-previous) t]
;;;     ["parent (P)" (call-or-eval 'imps-parent) t]
;;;     ["first child (C)" (call-or-eval 'imps-first-child) t]
;;;     ["next sibling (S)" (call-or-eval 'imps-next-sibling )t])
;;;    ("TeX"
;;;     ["xview sqn (x)" (call-or-eval 'sqn-xview) t]
;;;     ["xview dg (X)" (call-or-eval 'dg-xview-dg) t]
;;;     ["xview thm" (call-or-eval 'imps-xview-theorem) t])))

(defconst imps-menubar (append
			imps-fundamental-panes
			scheme-mode-panes
			imps-dg-panes
			imps-proof-panes
			(list ["XEmacs" imps-menu-toggle-menubar t])))

(defun imps-reset-menubar ()
  (interactive)
  (set-buffer-menubar imps-menubar))


(defun imps-menu-toggle-menubar ()
  (interactive)
  (set-buffer-menubar
   (cond ((equal current-menubar imps-menubar) imps-default-menubar)
	 (t imps-menubar))))
     

(defun imps-x-command-menu (arg)
  (interactive "P")
  (let ((sqn-no (current-sqn-no)))
    (message "Updating Command Menu...")
    (let ((commands 
	   (get-literal-from-tea 
	    (format "(applicable-commands (sequent-unhash %d))"
		    sqn-no))))
      
      (message "Done.")
      (popup-menu
       (cons "Commands"
	     (mapcar
	      '(lambda (x)
		 (vector x
			 (car (read-from-string 
			       (format "(call-or-eval '(dg-apply-command \"%s\" '(%d)))"
				       x
				       sqn-no)))
			 :keys (command-key x)))
	      commands))))))

(defun imps-x-special-command-menu (arg)
  (interactive "P")
  (let ((sqn-no (current-sqn-no)))
    (message "Updating Command Menu...")
    (let ((commands 
	   (get-literal-from-tea 
	    (format "(applicable-special-commands (sequent-unhash %d))"
		    sqn-no))))
      
      (message "Done.")
      (popup-menu
       (cons "Commands"
	     (append
	      '(["apply-macete (without minor premises)" (call-or-eval 'apply-macete-menu) t]
		["apply-macete-locally" (call-or-eval 'apply-macete-locally-menu) t]
		["apply-macete-locally-with-minor-premises" (call-or-eval 'apply-macete-locally-with-minor-premises-menu) t]
		["apply-macete-with-minor-premises" (call-or-eval 'apply-macete-with-minor-premises-menu) t]
		"--"
		)
	      
	      (mapcar
	       '(lambda (x)
		  (vector x
			  (car (read-from-string 
				(format "(dg-apply-command \"%s\" '(%d))"
					x
					sqn-no)))
			  :keys (command-key x)))
	       commands)))))))

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
  (let ((sqn-no (current-sqn-no)))
    (message "Updating Macete Menu...")
    (let ((macetes 
	   (sort
	   (get-literal-from-tea 
	    (format "(applicable-macetes-for-sqn (sequent-unhash %d))" sqn-no))
	   'string-lessp)))
      
      (message "Done.")
      (if macetes
	  (popup-menu
	   (cons "Macetes "
		 (mapcar '(lambda (x)
			    (vector x 
				    (` (apply-macete-command
					(, macete-command) (, x) (, sqn-no)))
				    t))
			 macetes)))
	
	(message "No applicable macetes!")))))

(defun apply-macete-command (macete-command macete sqn-no)
  (let ((*macete-from-menu*
	(car (read-from-string macete))))
    (dg-apply-command macete-command (list sqn-no))))

;;;(defun imps-reset-imps-program (arg)
;;;  (interactive "P")
;;;  (let ((in-imps-program-dir (directory-files (in-vicinity imps-source-files "../executables") t))
;;;	(file-menu-spec '()))
;;;    (mapcar '(lambda (x) (if (null (car (file-attributes x)))
;;;			     (setq file-menu-spec (cons (vector x (` (setq imps-program-name (, x))) t) file-menu-spec))))
;;;	    in-imps-program-dir)
;;;    (popup-menu (cons "-imps-programs-" file-menu-spec))))

(defun imps-status (arg)
  (interactive "P")
  (let ((stat (get-literal-from-tea "(status-of-theory-network-alist)")))
    (message (mapconcat '(lambda (x) (concat (symbol-name (car x)) "=" (format "%d" (cdr x))
					     ))  stat " "))))
(defun set-current-theory (arg)
  (interactive "P")
  (let ((theories
	 (sort
	  (get-literal-from-tea 
	   "(theory-names-in-global-theory-table)")
	  'string-lessp)))
    (let ((string (or arg (completing-read-or-get-from-x-menu "Theory: " (mapcar 'list theories) nil nil nil)))      )
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

    (let ((string (completing-read-or-get-from-x-menu "Section: " (mapcar 'list sections) nil nil nil)))      
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

    (let ((string (completing-read-or-get-from-x-menu "Section: " (mapcar 'list sections) nil nil nil)))      
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
	    "Section: "
	    (mapcar 'list sections)
	    nil nil nil)))      
      (and
       string
       (tea-eval-expression
	(format "(emacs-install-section-references '%s)" string))))))


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
;;;
;;;(defun examine-imps-object (type name)
;;;  (if name
;;;      (progn
;;;	(tea-eval-expression
;;;	 (format "(block
;;;             (pretty-print (name->%s '%s) (standard-output))
;;;             (newline (standard-output))
;;;             (pretty-print (let* ((obj (name->%s '%s)))
;;;                (map (lambda (sel) (list (selector-id sel) (sel obj))) (stype-selectors (structure-type obj)))) (standard-output)))"
;;;		 type name type name))
;;;	(pop-to-buffer "*tea*"))
;;;    nil))

;; (autoload 'imps-tutorial-formulas
;; 	  (concat (getenv "IMPS") "/../el/imps-tutorial")
;; 	  "Starts the IMPS interactive tutorial"
;; 	  t)

(defun imps-exercises (arg)
  (interactive "P")
  (require 'imps-tutorial)
  (let ((all-files (nreverse (sort (directory-files imps-exercise-directory) 'string-lessp)))
	(files '()))
    (mapcar '(lambda (x)
	       (if (string-match "\\.t$\\|\\.el$\\|\\.tex$" x)
		   (let ((y (substring x 0 (match-beginning 0))))
		     (setq files
			   (cons (vector y
					 (` (copy-and-find-exercise-file (, x)))
					 t) files)))))
	    all-files)
    (popup-menu  (cons "Exercise-Files" files))))

(defun copy-and-find-exercise-file (filename)
  (let ((imps-filename (concat imps-exercise-directory "/" filename))
	(copy-filename (concat "~/imps/theories/" filename)))
    (copy-file imps-filename  copy-filename 1)
    (find-file copy-filename)
    (delete-all-exercise-proofs)
    (save-buffer)
    (set-marker imps-exercise-already-sent-marker (point-min))
    (imps-exercise-next-target)))

;;This is redefined

(defun completing-read-or-get-from-x-menu (prompt table predicate require-match initial-input)

  (if (and (featurep 'imps-lucid-support)
	   (memq (event-type last-command-event)   '(button-release misc-user))
	   (listp table)
	   (<= (length table) *max-menu-size*))

;;Changed Tue Feb  3 14:58:28 EST 1998. Test for non-null value before returning.

      (progn (setq initial-input nil)
	     (or (imps-popup-menu (mapcar 'car table))
		 (error "Command aborted.")))
    (completing-read prompt table predicate require-match initial-input)))

;;;(defun read-one-index-from-minibuffer (prompt)
;;;  (catch 'minibuffer-read-tag
;;;
;;;    (let ((x-process-mouse-hook (if (and (or (featurep 'imps-x-support)
;;;					     (featurep 'imps-fsf-support)
;;;					     (featurep 'imps-lucid-support))
;;;					 (boundp 'assumption-number-and-exit-mouse-hook))
;;;				    assumption-number-and-exit-mouse-hook
;;;				  nil)))
;;;      (read-from-minibuffer prompt nil nil 't))))

(defconst assumption-number-and-exit-mouse-hook
  '(lambda (event)
     (let ((numb 
	    (save-excursion 
	      (mouse-count-occurrences-backwards
	       *formula-terminator-string*
	       assumption-assertion-separator
	       event ))))

       (if (numberp numb)
	   (throw 'minibuffer-read-tag numb)))))


(defun insert-in-minibuffer (str &optional erase)
  "Inserts STR in minibuffer."
  (set-buffer (window-buffer (minibuffer-window)))
  (if erase (erase-buffer))
  (insert str)
  (select-window (minibuffer-window)))

(defun insert-in-minibuffer-and-exit (str &optional erase)
  "Inserts STR in minibuffer."
  (insert-in-minibuffer str erase)
  (exit-minibuffer))

(defun imps-popup-menu (l)
  (let ((response
	 (get-popup-menu-response
	  (cons "Menu"
		(append
		 (mapcar
		  '(lambda (x)
		     (vector x (list 'quote x) t))
		  l)
		 (list 	
		  "---"
		  (vector "Cancel" (list 'quote nil)  t)
		  ))))))
    (if response (funcall (event-function response) (event-object response))
      nil)))


;;;Additional mouse support for imps.

;;We assume formulas are separated by  *formula-terminator-string*:
(defvar *formula-terminator-string* "\n\n")

(defun x-mouse-activate-point-to-mouse (event)
  "Activate the region between point and mouse.  Copy text object at point or
mouse position into window system cut buffer.  Save in Emacs kill ring also." 
  (interactive "@e")
  (let* ((here (point))
	 (there
	  (save-excursion (mouse-set-point event) (point)))
	 (s (buffer-substring here there)))
    (x-own-clipboard s)
    (x-store-cutbuffer s)
    (copy-region-as-kill here there)
    (push-mark there)
    (zmacs-activate-region)))

(defconst assumption-number-mouse-hook
  '(lambda (event)
     (let ((numb 
	    (save-excursion 
	      (mouse-count-occurrences-backwards
	       *formula-terminator-string*
	       assumption-assertion-separator
	       event ))))

       (if (numberp numb) (insert-in-minibuffer (format "%s " numb))))))


(defun count-occurrences-backwards (regexp)
  (save-excursion
    (let ((count 0)
	  (beg (point-min)))
      (while (re-search-backward regexp beg t)
	(setq count (1+ count)))
      count)))

(defun mouse-count-occurrences-backwards (terminator boundary event)
  (save-excursion
    (save-window-excursion
      (mouse-set-point event)
      (if (eq (current-buffer) (dgr-sqn-buffer))
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
	(progn (message "Mouse is in wrong buffer!") (ding) nil)))))


;;;Grabbing expressions with the mouse:

(defconst expression-grabber-mouse-hook
  'mouse-locate-containing-expression)

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

(defun mouse-locate-containing-expression (event)
  (save-excursion
    (save-window-excursion
      (mouse-set-point event)
      (let ((expr (locate-containing-expression)))
	(cond ((null expr) (ding) (message "Not pointing to anything which is recognizably an expression.") nil)
	      (t (throw 'minibuffer-read-tag expr)))))))

;(defun mouse-locate-containing-expression (event)
;  (save-excursion
;    (save-window-excursion
;      (mouse-set-point event)
;      (let ((expr (locate-containing-expression)))
;	(cond ((null expr) (ding) (message "Not pointing to anything which is recognizably an expression.") nil)
;	      (t (insert-in-minibuffer expr t))))))
;  (select-window (minibuffer-window)))


;;Toolbar stuff:

(make-variable-buffer-local 'imps-initial-toolbar-save)

(set-default 'imps-initial-toolbar-save
  '(find-file dired save-buffer x-kill-primary-selection x-copy-primary-selection x-yank-clipboard-selection undo query-replace))


(defvar imps-toolbar-directory  
  (expand-file-name (in-vicinity imps-source-files "../el/toolbar")))

(defun imps-filter-toolbar-spec (toolbar-spec)
  (let ((accum '()))
    (while toolbar-spec
      (if (memq (aref (car toolbar-spec) 1) imps-initial-toolbar-save)
	  (setq accum (cons (car toolbar-spec) accum)))
      (setq toolbar-spec (cdr toolbar-spec)))
    (nreverse accum)))

(defun imps-set-buffer-toolbar ()
  (let ((glph-list 
	 (mapcar (function (lambda(x) 
			     (and x
				  (let ((glf (make-glyph)))
				    (set-glyph-image 
				     glf
				     (make-image-specifier (vector (nth 0 x) ':file (format "%s/%s.%s" imps-toolbar-directory (nth 1 x) (nth 0 x)))))
				    (vector (list glf) (nth 2 x) 't (nth 3 x))))))
		 (get major-mode 'mode-toolbar-icons))))   
    (set-specifier default-toolbar (append (if (get major-mode 'initial-toolbar-spec)
					       (imps-filter-toolbar-spec initial-toolbar-spec)
					     nil)
					   glph-list)
		   (current-buffer))))

(setq dg-mode-hook '(set-local-buttons-hook imps-set-buffer-toolbar imps-reset-menubar))

(setq sqn-mode-hook '(set-local-buttons-hook imps-set-buffer-toolbar imps-reset-menubar))

(put 'sqn-mode 'mode-toolbar-icons 
	   '((xpm bang imps-x-command-menu "apply a command") 
	     (xpm breakup dg-direct-and-antecedent-inference-strategy "Break up the formula")
	     (xpm macete apply-macete-with-minor-premises-menu "Apply a macete")
	     (xpm simplify dg-simplify "Simplify current node")
	     ()
	     (xpm exercise imps-next-micro-exercise "Start Micro Exercise (or Next micro exercise)")
	     (xpm home-up  imps-home "Return to IMPS home window")
	     (xpm tea imps-tea "Go to *tea* buffer")
	     (xpm sqn imps-sqn "Go to *Sequent-node* buffer")
	     (xpm tex sqn-xview "View formatted current sequent node")
	     (xpm prev sqn-display-previous "Display previous sequent")
	     (xpm next sqn-display-next "Display next sequent")
	     (xpm parent imps-parent "Visit parent node")
	     (xpm child imps-first-child "Visit first child node")))

(put 'dg-mode 'mode-toolbar-icons 
	   '((xpm bang imps-x-command-menu "apply a command") 
	     (xpm breakup dg-direct-and-antecedent-inference-strategy "Break up the formula")
	     (xpm macete apply-macete-with-minor-premises-menu "Apply a macete")
	     (xpm simplify dg-simplify "Simplify current node")
	     ()
	     (xpm exercise imps-next-micro-exercise "Start Micro Exercise (or Next micro exercise)")
	     (xpm home-up  imps-home "Return to IMPS home window")
	     (xpm tea imps-tea "Go to *tea* buffer")
	     (xpm sqn imps-sqn "Go to *Sequent-node* buffer")
	     (xpm tex sqn-xview "View formatted current sequent node")
	     (xpm prev sqn-display-previous "Display previous sequent")
	     (xpm next sqn-display-next "Display next sequent")
	     (xpm parent imps-parent "Visit parent node")
	     (xpm child imps-first-child "Visit first child node")))

(put 'inferior-tea-mode 'mode-toolbar-icons 
	   '((xpm startdg imps-start-deduction "Start a new deduction") 
	     (xpm section imps-load-section "Loads a section")
	     (xpm theory set-current-theory "Sets the current theory")
	     () 
	     (xpm home-up  imps-home "Return to IMPS home window")
	     (xpm tea imps-tea "Go to *tea* buffer")
	     (xpm sqn imps-sqn "Go to *Sequent-node* buffer")))

(add-hook 'scheme-mode-hook 'set-local-buttons-hook t)
(add-hook 'scheme-mode-hook 'imps-reset-menubar t)
(add-hook 'df-listing-mode-hook 'set-local-buttons-hook t)
(add-hook 'df-listing-mode-hook 'imps-reset-menubar t)

(setq inferior-tea-mode-hook '(imps-set-buffer-toolbar set-local-buttons-hook imps-reset-menubar))


 

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    
