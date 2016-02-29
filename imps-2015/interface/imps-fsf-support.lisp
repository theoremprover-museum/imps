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



(provide 'imps-fsf-support)

(defconst imps-exercise-directory (in-vicinity imps-source-files "../exercises"))
;; (defconst imps-exercise-directory (concat (getenv "THEORIES") "/exercises"))
;; Changed by W. Farmer Tue May 28 16:14:40 EDT 1996


(defun set-local-buttons-hook ()
  (local-set-key [mouse-3] 'run-imps-mouse-hooks))

(defun run-imps-mouse-hooks (event)
  (interactive "@e")
  (funcall x-process-mouse-hook event)
  (setq this-command x-process-mouse-hook))

(defvar x-process-mouse-hook 'mouse-save-then-kill)

(defvar *menu-invocation-symbols* '())

(defun menu-invoked-p ()
  (memq last-command-event *menu-invocation-symbols*))

;;;(defun imps-reset-menubar ()
;;;  (interactive)
;;;  (make-local-menu-bar
;;;   (append
;;;    (if  (or (eq major-mode 'sqn-mode) (eq major-mode 'dg-mode))
;;;	imps-dg-panes
;;;      nil)
;;;    imps-proof-panes
;;;    imps-fundamental-panes
;;;    (if (eq major-mode 'scheme-mode)
;;;	scheme-mode-panes
;;;      nil))))

(defun imps-reset-menubar ()
  (interactive)
  (make-menu-bar
   (append
    imps-fundamental-panes
    scheme-mode-panes
    imps-dg-panes
    imps-proof-panes
    )
   'local
   ))

(defun keymap-range (local-or-global)
  (if (eq local-or-global 'local)
      'local-set-key
    'global-set-key))
    


(defun make-menu-bar (spec local-or-global)
  "Build a menu-bar from a SPECIFICATION. This consists of
   a list
      (
         (TITLE-string-A (option-1 function-1) (option-2 function-2))
         (TITLE-string-B (option-1 function-1) (option-2 function-2))
      )"
  (let ((menubar (make-sparse-keymap "menu-bar")))
    (funcall (keymap-range local-or-global) [menu-bar] menubar)
    (mapcar 
     '(lambda (x) (make-pulldown-menu x local-or-global))
     (reverse spec))))

;;(make-menu-bar scheme-mode-map '(("IMPS" ("start imps" run-imps) ("Doctor" doctor))))

(defun make-pulldown-menu (pd-spec local-or-global) ;;pd=pulldown
  (let ((pd-keymap (make-sparse-keymap (car pd-spec)))
	(local-num 0))

    (funcall (keymap-range local-or-global)
	     (vector 'menu-bar (read (downcase (car pd-spec))))
	     (cons (car pd-spec) pd-keymap))
    (mapcar 
     '(lambda (option)
	(let ((sym (read (concat local-num "-" (downcase (car option))))))
	  (setq local-num (+ 1 local-num))
	  (or (memq sym *menu-invocation-symbols*)
	      (setq *menu-invocation-symbols* (cons sym *menu-invocation-symbols*)))
	  (define-key pd-keymap (vector sym)
	    (cons (car option) (car (cdr option))))))
     (reverse (cdr pd-spec)))))
	  

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

(defconst imps-proof-panes 
  '(
    ("DG"
     ("Start dg" imps-start-deduction)
;;
;;   ("Start another dg" imps-new-start-deduction)
;; 
     ("Update dg display" dg-update-sqn-and-dg)
     ("Verbosely update dg display" verbosely-dg-update-sqn-and-dg)

     ("Jump to dg" sqn-display-dg-chunk)
     ("Jump to sqn" dg-display-sqn)
     ("Read and start dg" imps-read-and-start-deduction)))
  )

(defun verbosely-dg-update-sqn-and-dg ()
  "Update deduction graph display including display of grounded nodes and their
descendents."
  (interactive)
  (dg-update-sqn-and-dg t))


(defconst imps-fundamental-panes
  (cons
   (cons
    "IMPS-Help"
    (cons
     (list "Help" menu-bar-help-menu)
     '(("IMPS manual entry"   imps-manual-entry)
       ("Find def-form" imps-find-definition)
;;       ("Check expression syntax" check-imps-syntax-of-expression)
       ("Exercises" imps-exercises)
       ;;   ("Insert proof of next theorem" locate-and-insert-proof)
       ("Current exercise: Next Problem" imps-exercise-next-target)
       ("Restart exercise in Current Buffer"
	imps-exercise-start-in-current-file)
       ("Next micro exercise" imps-next-micro-exercise)
       ("Previous micro exercise" imps-previous-micro-exercise)
       ("Restart micro exercise" imps-repeat-micro-exercise))))
   
   '(    
     ("General"
      ("Set current theory" set-current-theory)
      ("Load IMPS file" imps-load-file)
      ("Reset load default dir" imps-reset-current-directory)
      ("Load section" imps-load-section)
;;      ("Load references for section" imps-load-section-references)
      ("Quick-load section" imps-quick-load-section)
      ("Theory network status" imps-status)
;;      ("Examine theory interpretation" examine-theory-interpretation)
;;      ("Reset imps-program" imps-reset-imps-program)
      ("Interrupt IMPS" interrupt-tea-process)
      ("Continue IMPS"  continue-tea-process)
      ("Toggle sound effects" imps-toggle-sound-effects)
      ("Font lock" font-lock-mode)
      ("Reset menu size"
       (lambda (arg) "Reset the maximum number of entries which can apppear in apopup menu."
	 (interactive "nMaximum Number of Menu Entries: " )
	 (setq *max-menu-size* arg)))
      ("Run IMPS" run-imps)
      ("Quit IMPS" quit-imps)))))

'(This was formerly:

       (defconst imps-fundamental-panes
	 '(
	   ("IMPS-Help"
	    ("Help"  menu-bar-help-menu)
	  
	    ("IMPS manual entry"   imps-manual-entry)
	    ("Find def-form" imps-find-definition)
	    ("Check expression syntax" check-imps-syntax-of-expression)
	    ("Exercises" imps-exercises)
	    ;;   ("Insert proof of next theorem" locate-and-insert-proof)
	    ("Current exercise: Next Problem" imps-exercise-next-target)
	    ("Restart exercise in Current Buffer"
	     imps-exercise-start-in-current-file)
	    ("Next micro exercise" imps-next-micro-exercise)
	    ("Previous micro exercise" imps-previous-micro-exercise)
	    ("Restart micro exercise" imps-repeat-micro-exercise))
    
	   ("General"
	    ("Set current theory" set-current-theory)
	    ("Load IMPS file" imps-load-file)
	    ("Reset load default dir" imps-reset-current-directory)
	    ("Load section" imps-load-section)
	    ("Load references for section" imps-load-section-references)
	    ("Quick-load section" imps-quick-load-section)
	    ("Theory network status" imps-status)
;;	    ("Examine theory interpretation" examine-theory-interpretation)
;;	    ("Reset imps-program" imps-reset-imps-program)
	    ("Interrupt IMPS" interrupt-tea-process)
	    ("Continue IMPS"  continue-tea-process)
	    ("Toggle sound effects" imps-toggle-sound-effects)
	    ("Font lock" font-lock-mode)
	    ("Reset menu size"
	     (lambda (arg) "Reset the maximum number of entries which can apppear in apopup menu."
	       (interactive "nMaximum Number of Menu Entries: " )
	       (setq *max-menu-size* arg)))
	    ("Run IMPS" run-imps)
	    ("Quit IMPS" quit-imps)))))

(defun some-sqn-live-p()
  (save-excursion
    (catch 'found
      (mapcar '(lambda (b) (set-buffer b)
		 (if (eq major-mode 'sqn-mode) (throw 'found t)))
	      (buffer-list))
      nil)))

(mapcar '(lambda (sym)
	   (put sym 'menu-enable '(some-sqn-live-p)))
	'(dg-update-sqn-and-dg
	  verbosely-dg-update-sqn-and-dg
	  sqn-display-dg-chunk
	  dg-display-sqn
	  imps-read-and-start-deduction
	  imps-x-command-menu
	  apply-macete-with-minor-premises-menu
	  imps-x-special-command-menu
	  imps-macete-menu
	  imps-comment-latest-entry
	  
	  imps-first-unsupported-relative
	  imps-first-unsupported-descendent
	  sqn-select
	  sqn-display-max
	  sqn-display-next
	  sqn-display-previous
	  imps-parent
	  imps-first-child
	  imps-next-sibling 
	  sqn-xview
	  imps-xview-sqns
	  dg-xview-dg
	  imps-save-tex-output))

(defconst scheme-mode-panes
  '(("Def-forms"
     ("Evaluate def-form" tea-send-definition)
     ("Evaluate def-form; go to tea" tea-send-definition-and-go)
     ("Insert def-form template" insert-template)
     ("Show this def-form" df-show-current-def-form)
     ("Show next def-from" df-show-next-def-form)
     ("Show previous def-form" df-show-previous-def-form)
     ("Evaluate def-form" df-evaluate-def-form)
     ("List def-forms" df-list-create-or-restore)
;;   ("List def-forms" df-list-in-buffer)
     ("Quit listing def-forms" df-quit))
    ("Scripts"
     ("Insert proof script" imps-insert-current-proof)
     ("Execute proof line" imps-assistant-execute-line)
     ("Execute region" imps-assistant-execute-region)
     ("Execute script of current def-form" imps-run-current-proof-script)
     ("Autoblocking on" turn-on-script-autoblocking)
     ("Autoblocking off" turn-off-script-autoblocking))))

(mapcar '(lambda (sym)
	   (put sym 'menu-enable '(eq major-mode 'df-listing-mode)))
	'(df-show-current-def-form
	  df-show-next-def-form
	  df-show-previous-def-form
	  df-evaluate-def-form
	  df-quit))

(mapcar '(lambda (sym)
	  (put sym 'menu-enable '(eq major-mode 'scheme-mode)))
	'(tea-send-definition
	  tea-send-definition-and-go
	  df-list-in-buffer))

(mapcar '(lambda (sym)
	  (put sym 'menu-enable '(eq major-mode 'scheme-mode)))
	'(sw-process-file 
	  sw-process-file-with-proofs
	  sw-un-process-file 
	  sw-make sw-set-up-directory))

(put 'sqn-display-dg-chunk 'menu-enable '(eq major-mode 'sqn-mode))
(put 'dg-display-sqn 'menu-enable '(eq major-mode 'dg-mode))

(put 'turn-on-script-autoblocking 'menu-enable '(null autoblock-scripts))
(put 'turn-off-script-autoblocking 'menu-enable 'autoblock-scripts)

(defconst imps-dg-panes
  '(("Extend-DG"
     ("Commands" imps-x-command-menu)
     ("Special commands" imps-x-special-command-menu)
     ("Macetes (with minor premises)" apply-macete-with-minor-premises-menu)
     ("Macete description" imps-macete-menu)
     ("Comment preceding entry"  imps-comment-latest-entry))
    ("Nodes"
     ("First unsupported relative" imps-first-unsupported-relative)
     ("First unsupported descendent" imps-first-unsupported-descendent)
     ("Sqn by number" sqn-select)
     ("Maximum sqn" sqn-display-max)
     ("Next sqn" sqn-display-next)
     ("Previous sqn" sqn-display-previous)
     ("Parent" imps-parent)
     ("First child" imps-first-child)
     ("Next sibling" imps-next-sibling ))
    ("TeX"
     ("Xview sqn" sqn-xview)
     ("Xview sqns" imps-xview-sqns)
     ("Xview dg" dg-xview-dg)
     ("Xview thm" imps-xview-theorem)
     ("Xview macete" imps-xview-macete)
     ("Build and xview expression" build-and-xview-string)
     ("Xview theory" imps-xview-theory)
     ("Schemeweb on current file" sw-process-file)
     ("Schemeweb with proofs on current file" sw-process-file-with-proofs)
     ("Undo Schemeweb on current file" sw-un-process-file)
     ("Run make for Schemeweb" sw-make)
     ("Set up directory for Schemeweb" sw-set-up-directory)
     ("Save last tex output" imps-save-tex-output)
     ("Print tex output" imps-print-tex-output))))

(defun imps-popup-menu (arg spec)
  (if (null arg) (setq arg '(0 0)))
  (x-popup-menu (list arg (selected-window)) spec))

(defun imps-x-command-menu (arg)
  "Brings up a menu of proof commands applicable to the current sequent node.
Mouse selection of entry invokes the command."  
  (interactive "P")
  (let ((sqn-no (current-sqn-no))
	(imps-mouse-call-p t))
    (message "Updating Command Menu...")
    (let ((commands 
	   (get-literal-from-tea 
	    (format "(applicable-commands (sequent-unhash %d))" sqn-no))))
      
      (message "Done.")
      (let ((string (imps-popup-menu
		     '()
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

  "Brings up a menu of less frequently used proof commands applicable to 
the current sequent node. Mouse selection of entry invokes the command. "
  (interactive "P")
  (let ((sqn-no (current-sqn-no))
	(imps-mouse-call-p t))
    (message "Updating Special Command Menu...")
    (let ((commands 
	   (get-literal-from-tea 
	    (format "(applicable-special-commands (sequent-unhash %d))" sqn-no))))
      (message "Done.")
      (let ((string (imps-popup-menu
		     '()
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

    "Brings up a menu of macetes applicable to the current sequent node. 
Mouse selection of entry invokes the macete posting minor premises
as additional subgoals to be proved. 

A macete is a theorem or group of theorems."
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
	  (let ((string (imps-popup-menu
			 '()
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
  "Pop up a menu of imps buffers for selection with the mouse."
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


;;;(defun imps-reset-imps-program (arg)
;;;  (interactive "P")
;;;  (let ((in-imps-program-dir (directory-files (in-vicinity imps-source-files "../executables") t))
;;;	(file-menu-spec '()))
;;;    (mapcar '(lambda (x) (if (null (car (file-attributes x)))
;;;			     (setq file-menu-spec (cons (cons x x) file-menu-spec))))
;;;	    in-imps-program-dir)
;;;    (let ((selection
;;;	   (imps-popup-menu '()
;;;			 (list "Imps-Programs"
;;;			       (cons "-imps-programs-"
;;;				     file-menu-spec)))))
;;;      (setq imps-program-name selection))))


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

;;;(defun examine-imps-object (type name fields)
;;;  (tea-eval-expression
;;;   (format "(block
;;;             (pretty-print (name->%s '%s) (standard-output))
;;;             (newline (standard-output))
;;;             (pretty-print (let* ((obj (name->%s '%s)))
;;;                (map (lambda (sel)  (stype-selectors (structure-type obj)))) (standard-output)))"
;;;	   type name type name))
;;;  (pop-to-buffer "*tea*"))

;; (autoload 'imps-tutorial-formulas
;; 	  (concat (getenv "IMPS") "/../el/imps-tutorial")
;; 	  "Starts the IMPS interactive tutorial"
;; 	  t)


(defun imps-exercises (arg)
  "Select a buffer of IMPS exercises which can be freely edited. Buffer is
associated with a file in the directory ~/imps/theories."
  (interactive "P")
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
;;	    (delete-all-exercise-proofs)
;;	    (save-buffer)

	    (set-marker imps-exercise-already-sent-marker (point-min))
	    (imps-exercise-next-target))))))

(defun set-current-theory (arg)
  "Set the current theory to a new value. System prompts the user with
a menu of currently loaded theories. The current theory affects the behavior
of IMPS in a number of ways  

  1. Any expression that is read in belongs to the language of the current
theory.

  2. Any proof begun in the current theory may use axioms or previously
proved theorems of this theory."

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
  "Load a new section. System prompts the user with a menu of sections.
A section is a body of knowledge which includes theories, definitions and
theorems."

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
  "Quick-load a new section, that is load the section without
those theorems marked as lemmas and  without checking that translations
marked \"force-under-quick-load\" are indeed translations. System prompts
the user with a menu of sections. A section is a body of knowledge which includes theories, definitions and theorems."
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

;;;

(defun insert-in-minibuffer (str &optional erase)
  "Inserts STR in minibuffer."
  (set-buffer (window-buffer (minibuffer-window)))
  (if erase (erase-buffer))
  (insert str)
  (select-window (minibuffer-window)))

(defvar *formula-terminator-string* "\n\n")

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

;; (setq dg-mode-hook '(set-local-buttons-hook imps-reset-menubar))
;; 
;; (setq sqn-mode-hook '(set-local-buttons-hook imps-reset-menubar))
;; 
;; (setq scheme-mode-hook '(set-local-buttons-hook imps-reset-menubar))

;;(make-menu-bar emacs-panes 'global)

(setq menu-bar-final-items '(buffer file edit help))

(mapcar
 (function
  (lambda (mode)
    (add-hook mode 'set-local-buttons-hook t)
    (add-hook mode 'imps-reset-menubar t)))
 '(dg-mode-hook sqn-mode-hook scheme-mode-hook inferior-tea-mode-hook df-listing-mode-hook))

;; (add-hook 'scheme-mode-hook 'set-local-buttons-hook t)
;; (add-hook 'scheme-mode-hook 'imps-reset-menubar t)

(setq inferior-tea-mode-hook '(set-local-buttons-hook imps-reset-menubar))

;;; Similar to emacs 18

(defun completing-read-or-get-from-x-menu 
  (prompt table predicate require-match initial-input)
  (if (and (featurep 'imps-fsf-support)
	   (menu-invoked-p)
	   (listp table)
	   (<= (length table) *max-menu-size*))
      (let ((string (imps-popup-menu
		     '()
		     (list "Menu"
			   (cons (replace-chars-in-string prompt 58 32)
				 (mapcar
				  '(lambda (x)
				     (cons x x))
				  (mapcar 'car table)))))))
	(if string string (error "Command aborted.")))
    (completing-read prompt table predicate require-match initial-input)))

;;;These two are put in experimentally

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


(defun build-and-xview-string (arg)
  (interactive "p")
  (let ((formula

	 ;;Allow grabbing of expressions with mouse (if desired!)

	 (let ((x-process-mouse-hook (if (boundp 'expression-grabber-mouse-hook)
					 expression-grabber-mouse-hook
				       nil)))

	   (imps-read-from-minibuffer "Formula or reference number: " nil
				      inferior-tea-minibuffer-map))))
    (let ((ref-by-number-p
	    (and (not (string-match "^[ ]*#" formula))
		 (numberp (car (read-from-string formula))))))
      (message
      (tea-eval-expression
       (format "(xview  (qr %s))"
	       (if (not ref-by-number-p)
		   (imps-input-quote-string-if-needed formula)
		 
		 ;;Remark: If "formula" is a string, tea will wrap a (qr ..) around it before
		 ;;evaluating it. Otherwise tea will evaluate it directly.

		 (concat "(imps-ref " formula ")"))))))))


(defun imps-xview-theory (arg)
  (interactive "P")
  (let ((theories
	 (sort
	  (get-literal-from-tea 
	   "(theory-names-in-global-theory-table)")
	  'string-lessp)))
    (let ((string (completing-read-or-get-from-x-menu "Theory: " (mapcar 'list theories) nil nil nil)))      
      (if string (tea-eval-expression
		  (format "(xview (name->theory '%s))" string))
	nil))))

(defun sw-make (target)
  "Call make with one of the targets tangled,woven."
  (interactive
   (list
    (completing-read
     "Make tangled/woven: "
     '(("tangled") ("woven")))))
  (compile (format "make %s" target)))
     
(fset 'pprint #'pp)

(fset 'mapc #'mapcar)
    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    
