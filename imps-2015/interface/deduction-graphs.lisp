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



;; Support for *Sequent Nodes* and *Deduction* buffers to display the sequent
;;; nodes of a deduction-graph.

;;;(require 'process-filter)
;;;(require 'sqns)
;;;(require 'imps-edit)
;;;(require 'protocols)
(provide 'deduction-graphs)


(defvar dg-display-hook nil)
(defvar micro-exercise-p nil "Currently working on micro-exercise")
;;; Here is a dg display hook that moves the point to the end of the buffer.
(defun dg-move-to-end-of-dg ()
  (goto-char (point-max)))
;;;;

(defun always (s) t)

(defun make-sqn-mode-map ()
  (let ((map (copy-keymap scheme-mode-map)))
    (define-key map ">" 'sqn-display-max)
    (define-key map "j" 'sqn-display-jump)
    (define-key map "n" 'sqn-display-next)
    (define-key map "p" 'sqn-display-previous)
    (define-key map "l" 'sqn-redisplay-last-seen)
    (define-key map "." 'sqn-display-dg-chunk)
    (define-key map "h" 'sqn-hide)
    (define-key map "x" 'sqn-xview)
    (define-key map "X" 'dg-xview-dg)
    (define-key map "d" 'dg-direct-inference)
    (define-key map "D" 'dg-direct-and-antecedent-inference-strategy)
    (define-key map "b" 'dg-backchain)
    (define-key map "m" 'dg-apply-macete)
    (define-key map "c" 'dg-contrapose)
    (define-key map "@" 'dg-incorporate-antecedent)
    (define-key map "a" 'dg-antecedent-inference)
    (define-key map "A" 'dg-antecedent-inference-strategy)
    (define-key map "w" 'dg-weaken)
    (define-key map "e" 'sqn-edit-sqn)
    (define-key map "i" 'dg-induction)
    (define-key map "u" 'dg-unfold-single-defined-constant)
    (define-key map "U" 'dg-unfold-single-defined-constant-globally)
    (define-key map "\C-cU" 'dg-unfold-defined-constants)

    (define-key map "~" 'dg-extensionality)
    (define-key map "&" 'dg-cut-with-single-formula)
    (define-key map "\C-cb" 'dg-beta-reduce-repeatedly)
    (define-key map "f" 'dg-force-substitution)
    (define-key map "r" 'dg-raise-conditional)

    (define-key map "\C-c\C-c" 'dg-post-cmpn)
    (define-key map "\C-c\C-s" 'dg-simplify)    
    (define-key map "\C-cs" 'dg-simplify)
    (define-key map "!" 'dg-apply-command)
    (define-key map "\C-c!" 'dg-apply-command-multiply)
    (define-key map "s" 'dg-apply-command)
    (define-key map "?" 'imps-command-menu)
    (define-key map "\C-c?" 'imps-macete-menu-xless)
    ;; Tree-oriented motion commands -- temporary bindings
    ;; let's see how they work.
    ;;
    (define-key map "P" 'imps-parent)
    (define-key map "F" 'imps-first-unsupported-relative)
    (define-key map "C" 'imps-first-child)
    (define-key map "S" 'imps-next-sibling)
    map))

(defvar sqn-mode-map (make-sqn-mode-map))

(defun make-dg-mode-map ()
  (let ((map (copy-keymap scheme-mode-map)))
    (define-key map ">" 'sqn-display-max)
    (define-key map "j" 'sqn-display-jump)
    (define-key map "n" 'sqn-display-next)
    (define-key map "p" 'sqn-display-previous)
    (define-key map "l" 'sqn-redisplay-last-seen)
    (define-key map "." 'dg-display-sqn)
    (define-key map "x" 'dg-xview-sqn)
    (define-key map "X" 'dg-xview-dg)
    (define-key map "h" 'dg-hide)
    (define-key map "H" 'dg-hide-region)
    (define-key map "d" 'dg-direct-inference)
    (define-key map "D" 'dg-direct-and-antecedent-inference-strategy)
    (define-key map "b" 'dg-backchain)
    (define-key map "m" 'dg-apply-macete)
    (define-key map "c" 'dg-contrapose)
    (define-key map "@" 'dg-incorporate-antecedent)
    (define-key map "a" 'dg-antecedent-inference)
    (define-key map "A" 'dg-antecedent-inference-strategy)
    (define-key map "w" 'dg-weaken)
    (define-key map "i" 'dg-induction)
    (define-key map "\C-cU" 'dg-unfold-defined-constants)

    (define-key map "~" 'dg-extensionality)
    (define-key map "&" 'dg-cut-with-single-formula)
    (define-key map "\C-cb" 'dg-beta-reduce-repeatedly)
    (define-key map "f" 'dg-force-substitution)
    (define-key map "r" 'dg-raise-conditional)

    (define-key map "e" 'sqn-edit-sqn)
    (define-key map "\C-c\C-c" 'dg-post-cmpn)
    (define-key map "\C-c\C-s" 'dg-simplify)
    (define-key map "\C-cs" 'dg-simplify)
    (define-key map "!" 'dg-apply-command)
    (define-key map "\C-c!" 'dg-apply-command-multiply)
    (define-key map "s" 'dg-apply-command)
    (define-key map "?" 'imps-command-menu)
    (define-key map "\C-c?" 'imps-macete-menu)
    ;; Tree-oriented motion commands -- temporary bindings
    ;; let's see how they work.
    ;;
    (define-key map "P" 'imps-parent)
    (define-key map "F" 'imps-first-unsupported-relative)
    (define-key map "C" 'imps-first-child)
    (define-key map "S" 'imps-next-sibling)
    map))

(defvar dg-mode-map (make-dg-mode-map))

(fset 'sqn-buffer 'dgr-sqn-buffer)

(fset 'dg-buffer 'dgr-dg-buffer)

;;Changed by jt Sat Mar 21 20:58:39 EST 1998, to escape % for theory names:

(defun escape-percentages (str)
  (mapconcat '(lambda (x) (if (char-equal x ?%) "%%" (format "%c" x))) str ""))


;; Changed by jt Sun Mar 22 11:36:35 EST 1998. Make modeline formats for deduction  graph and
;; sequent node buffers more uniform.

(defun sqn-mode ()
  "Major mode for interacting with IMPS sequents. 
Commands:
\\{sqn-mode-map}\n"
  (setq major-mode 'sqn-mode)
  (setq mode-name "Seq Nodes") 
  (setq buffer-read-only t)
;;  (setq dg-number 1) ;;;vestigial
  (sqn-set-current-sqn 0)
  (setq mode-line-format
	(list "Theory: "
	      (escape-percentages (dgr-theory-name))
	      "  " 
	      '(25 t mode-line-process)
	      " " 
	      '(17 . "%b")
	       "  %3p %1*"))
  (run-hooks 'sqn-mode-hook))

(defun dg-mode ()
  "Major mode for interacting with IMPS deduction graphs.
Commands:
\\{dg-mode-map}\n"
  (use-local-map dg-mode-map)
  (setq major-mode 'dg-mode)
  (setq mode-name "Deduction Graph")
  (setq buffer-read-only t)
  (setq truncate-lines t)
  (setq mode-line-format
	(list "Theory: "
	      (escape-percentages (dgr-theory-name))
	      "  "
	      '(25 "")
	      " " 
	      '(17 . "%b")
	       "  %3p %1*"))
;  (setq dg-number 1) ;;vestigial
  (scheme-mode-variables)
  (run-hooks 'dg-mode-hook))

(defun dg-read-from-file (dg-buffer dg-file)
  (interactive "bdg-buffer: ")
  (set-buffer dg-buffer)
  (let ((buffer-read-only nil))
    (erase-buffer)
    (insert-file-contents
     (expand-file-name (substitute-in-file-name dg-file)))
    (goto-char (point-min))
    (let ((dg-sexp (read (current-buffer))))
      (erase-buffer)
      (pprint dg-sexp (current-buffer)))
    (if (not (null dg-display-hook))
	(run-hooks 'dg-display-hook))))

(defun dg-current-sqn ()
  (interactive)
  (save-excursion
    (condition-case tmp
	(progn
	  (beginning-of-enclosing-list)
	  (re-search-forward "-\\([0-9]+\\)") 
	  (car (read-from-string (buffer-substring (match-beginning 1) (match-end 1)))))
      (error
       1
       ))))


(defun current-sqn-no ()
  (cond ((eq major-mode 'dg-mode)
	 (dg-current-sqn))
	(t (dgr-current-sqn))))

(defun dg-display-sqn (pos)
  "Display the sqn currently under the cursor in the sqn buffer."
  (interactive "d")
  (let ((index (dg-current-sqn)))
    (switch-to-buffer-other-window (sqn-buffer))
    (sqn-display index)))
    
;; User level procedures follow
  
(defun sqn-hide (sqn-no)
  "Hide sequent node SQN."
  (interactive (list (current-sqn-no)))
  (tea-eval-and-update-sqn-and-dg
   (format "(sequent-node-hide (sequent-unhash %s))"
	   sqn-no)))
  
(defun dg-hide (sqn-no)
  "Hide sequent node SQN."
  (interactive (list (dg-current-sqn)))
  (tea-eval-and-update-sqn-and-dg 
   (format "(sequent-node-hide (sequent-unhash %s))"
	   sqn-no)))
 
(defun dg-hide-region (start end)
  (interactive "r")
  (let ((sqn-nos (integers-within-region start end)))
    (tea-eval-and-update-sqn-and-dg 
     (format "(map
	       (lambda (n)
		 (sequent-node-hide (sequent-unhash n)))
	       '%s)"
	     sqn-nos))))
 

(defun sqn-unhide (sqn-no)
  "Unhide sequent node SQN."
  (interactive (list (current-sqn-no)))
  (sequent-node-unhide (sequent-unhash sqn-no)))
  
(defun dg-unhide (sqn-no)
  "Unhide sequent node SQN."
  (interactive (list (dg-current-sqn)))
  (sequent-node-unhide (sequent-unhash sqn-no)))

(defun sqn-xview (sqn-no)
  "Run xview on the current SQN."
  (interactive (list (current-sqn-no)))
  (dg-xview-sqn sqn-no))
  
(defun dg-xview-sqn (sqn-no)
  "Run xview on the current SQN."
  (interactive
   (list (dg-current-sqn)))
  (message "Starting xview...")
  (xview (sequent-unhash sqn-no)))

(defun dg-xview-dg ()
  "Run xview on the Current DG."
  (message "Starting xview on deduction graph.") 
  (xview (current-dg)))

(defun imps-current-sqn ()
  (current-sqn-no))


;; Tree-oriented motion commands--

(defmacro def-imps-motion (emacs-name tea-proc)
  "Defun emacs-name to shift the *Sequent-nodes* display 
to the result of running tea-proc on the argument sqn-no."
  (let ((str (format "Display node produced by  %s  from argument sqn."
		     tea-proc)))
    (` (defun (, emacs-name) (sqn-no)
	 (, str)
	 (interactive (list (imps-current-sqn)))
	 (tea-eval-expression
	  (format "(emacs-display-sqn (%s (sequent-unhash %s)))"
		  '(,  tea-proc) sqn-no))))))

(def-imps-motion imps-parent sequent-node-parent)
(def-imps-motion imps-first-child sequent-node-first-child)
(def-imps-motion imps-next-sibling sequent-node-next-sibling)
(def-imps-motion imps-first-unsupported-descendent sequent-node-first-unsupported-descendent)
(def-imps-motion imps-first-unsupported-relative sequent-node-first-unsupported-relative)
(defun imps-first-unsupported ()
  "Display node produced by  sequent-node-first-unsupported-descendent  from sequent node 1"
  (interactive)
  (imps-first-unsupported-descendent 1))

;;;(defun dg-post-cmpn ()
;;;  (interactive)
;;;  (tea-eval-expression
;;;   (format "(bind (((emacs-dg) (dgrv-index->dg %d)))
;;;		  (emacs-display-cmpn
;;;		   (post-computation-node
;;;		    (sequent-unhash %d))))"
;;;	   dg-number (imps-current-sqn))))


;;Special calls:

(defun dg-direct-inference ()
  (interactive)
  (dg-apply-command "direct-inference" (list (current-sqn-no))))

(defun dg-contrapose () (interactive)
  (dg-apply-command "contrapose"  (list (current-sqn-no))))

(defun dg-backchain () (interactive)
  (dg-apply-command "backchain" (list (current-sqn-no))))

(defun dg-apply-macete ()
  (interactive)
  (dg-apply-command
   (if current-prefix-arg
       "apply-macete"
     "apply-macete-with-minor-premises")
   (list (current-sqn-no))))

(defun dg-incorporate-antecedent () (interactive)
  (dg-apply-command "incorporate-antecedent" (list (current-sqn-no)) ))

(defun dg-antecedent-inference () (interactive)
  (dg-apply-command "antecedent-inference" (list (current-sqn-no)) ))

(defun dg-weaken () (interactive)
  (dg-apply-command "weaken" (list (current-sqn-no)) ))

(defun dg-unfold-single-defined-constant () 
  (interactive) 
  (dg-apply-command "unfold-single-defined-constant" (list (current-sqn-no))))

(defun dg-unfold-single-defined-constant-globally () (interactive)
  (dg-apply-command "unfold-single-defined-constant-globally" (list (current-sqn-no))))

(defun dg-unfold-defined-constants () (interactive)
  (dg-apply-command "unfold-defined-constants" (list (current-sqn-no))))

(defun dg-simplify () (interactive)
  (dg-apply-command "simplify" (list (current-sqn-no))))

(defun dg-direct-inference-strategy ()
  (interactive)
  (dg-apply-command "direct-inference-strategy" (list (current-sqn-no))))

(defun dg-direct-and-antecedent-inference-strategy ()
  (interactive)
  (dg-apply-command "direct-and-antecedent-inference-strategy" (list (current-sqn-no))))

(defun dg-antecedent-inference-strategy ()
  (interactive)
  (dg-apply-command "antecedent-inference-strategy" (list (current-sqn-no))))

(defun dg-induction ()
  (interactive)
  (dg-apply-command "induction" (list (current-sqn-no))))

(defun dg-edit-and-post ()
  (interactive)
  (dg-apply-command "edit-and-post-sequent-node" (list (current-sqn-no))))

(defun dg-force-substitution ()
  (interactive)
  (dg-apply-command "force-substitution" (list (current-sqn-no))))

(defun dg-raise-conditional ()
  (interactive)
  (dg-apply-command "raise-conditional" (list (current-sqn-no))))

(defun dg-cut-with-single-formula ()
  (interactive)
  (dg-apply-command "cut-with-single-formula" (list (current-sqn-no))))

(defun dg-beta-reduce ()
  (interactive)
  (dg-apply-command "beta-reduce" (list (current-sqn-no))))

(defun dg-beta-reduce-repeatedly ()
  (interactive)
  (dg-apply-command "beta-reduce-repeatedly" (list (current-sqn-no))))

(defun dg-extensionality ()
  (interactive)
  (dg-apply-command "extensionality" (list (current-sqn-no))))
  
(defun dg-informal-justification ()
  (interactive)
  (dg-apply-command "informal-justification" (list (current-sqn-no))))

;;;COMMANDS:

(defun dg-apply-command (command &optional sqn-nos args)
  (interactive
   (list (imps-completing-read "Command name: "
			       imps-commands
			       'always
			       nil
			       nil)))
	 
  (catch 'apply-command-tag
    (let ((sqn-nos (if sqn-nos sqn-nos
		     (car (read-from-string (format "(%d)" (current-sqn-no))))))
	  (args (if args args
		  (save-excursion
		    (funcall (argument-retrieval-protocol command))))))
      (transmit-command-and-args command sqn-nos args))))

(defun dg-apply-command-multiply (command  &optional sqn-nos args)
  (interactive
   (list (imps-completing-read "Command name: "
			       imps-commands
			       'always
			       nil
			       nil)))
  (catch 'apply-command-tag
    (let ((sqn-nos (if sqn-nos sqn-nos
		     (read-from-minibuffer "Sequent nodes: "
					   (format "(%d)" (current-sqn-no))
					   nil t)))
	  (args (if args args
		  (save-excursion
		    (funcall (argument-retrieval-protocol command))))))
      (transmit-command-and-args command sqn-nos args))))

;;;(defun induction-arguments-retrieval-protocol ()
;;;  (let ((inductor (imps-completing-read "Inductor: " imps-inductors (function (lambda (s) t)) nil nil)))
;;;    (format "(list (name->inductor '%s) '(%s))" inductor (request-induction-variable))))


	       
;;;(defun instantiate-auto-transported-theorem-retrieval-protocol ()
;;;  "Add to the context of SQN the instance of the translation of THM-NAME under 
;;;   a suitable translation in which the universally quantified variables are replaced by 
;;;   TERM-STRINGS. "
;;;  (let ((theory (imps-completing-read "Source theory: "
;;;				 imps-obarray
;;;				 'kind-is-theory-p
;;;				 nil
;;;				 nil)))
;;;    (let ((theorem-name (imps-completing-read "Theorem name: "
;;;					 imps-obarray
;;;					 'kind-is-theorem-p
;;;					 nil
;;;					 nil)))
;;;      (let ((var-sorts (imps-get-theorem-var-sorts theorem-name)))
;;;	(format "(list '%s '(%s))"  
;;;		theorem-name
;;;		(collect-a-bunch-of-variable-instantiations (cdr available)))))))

;;;(defun symbol-retrieval-protocol ()
;;;  (format "(list '%s)" 
;;;	  (imps-read-from-minibuffer "Constant name: " "" nil t)))
(defun dg-update-sqn-and-dg (verbose)
  "Update the sqn and dg buffers by getting accurate info from IMPS."
  (interactive "P")
  (block (emacs-add-all-new-sqns (current-dg))
    (emacs-update-dg (current-dg))))

(defun verbosely-dg-update-sqn-and-dg ()
  "Update deduction graph display including display of grounded nodes and their
descendents."
  (interactive)
  (block (emacs-add-all-new-sqns (current-dg))
    (emacs-verbose-update-dg (current-dg))))

(fset 'update-sqn-and-dg 'dg-update-sqn-and-dg)

(defun tea-eval-and-update-sqn-and-dg (str)
  (message "Calling Tea...")
  (execute-call-from-emacs-and-update str))

(autoload 'imps-post "imps-edit"
	  "Send contents of buffer to IMPS process to post in deduction-graph"
	  t)

(autoload 'sequent-edit-mode "imps-edit"
	  "Major mode for editing sequent nodes for IMPS deduction graphs."
	  t)

(defun sqn-edit-sqn (fully-parenthesize)
  "Put current sqn into a buffer to edit.  Flag FULLY-PARENTHESIZE (prefix arg
if interactive) means put in all parentheses.  "
  (interactive "P")
  (if (and (not (eq major-mode 'sqn-mode))
	   (not (eq major-mode 'dg-mode)))
      (error "Not in sqn-mode or dg-mode"))
  (let ((sqn-index (current-sqn-no)))
    (setq imps-edit-window-configuration (current-window-configuration))
    (pop-to-buffer (get-buffer-create "*IMPS Sequent*"))
    (emacs-send-sqn-to-edit 
     (sequent-unhash sqn-index (if fully-parenthesize (true) (false))))))

(defun dg-edit-sqn (sqn-index fully-parenthesize)
  "Put sequent node with sqn-index-number SQN-INDEX into a buffer to edit"
  (interactive  
   (list (dg-current-sqn) current-prefix-arg))
  (if (not (eq major-mode 'dg-mode))
      (error "Not in dg-mode"))
    (setq imps-edit-window-configuration (current-window-configuration))
    (pop-to-buffer (get-buffer-create "*IMPS Sequent*"))
    (emacs-send-sqn-to-edit 
     (sequent-unhash (if fully-parenthesize (true) (false)))))

(defun imps-start-deduction ()
  "Start an IMPS deduction. System prompts for formula in the minibuffer. 
Formula may be entered in the minibuffer. If a window system is being used, 
formula may also be entered by clicking the right mouse button on an occurrence
of the formula within double quotes in an emacs buffer.

A deduction in IMPS is represented as a deduction-graph. The graph is
displayed in two buffers:

  1. One buffer displays individual sequents.

  2. The other buffer displays the graph."
 
  (interactive)

  (imps-read-from-minibuffer "Formula: ")
  (message "Setting up deduction graph display...")
  (imps-start-deduction-internal formula)))


(defun imps-start-deduction-internal (formula)    
  (clear-em) 
  (start-emacs-deduction (imps-input-quote-string-if-needed formula)))
		 
;;Remark: If "formula" is a string, tea will wrap a (qr ..) around it before
;;evaluating it. Otherwise tea will evaluate it directly.





(defconstant usage-names '(("macete")
			("transportable-macete")
			("rewrite")
			("d-r-value")
			("processor")
			("recursive-unfolding")
			("d-r-convergence"))
  "list of names of usages")

(defun retrieve-usage-list ()
  (let (usages new-string)
    (setq new-string
	  (imps-completing-read "First usage: "
			   usage-names 'always nil nil))
    (while (not (string= "" new-string))
      (setq usages (cons new-string usages))
      (setq new-string
	    (imps-completing-read "Next usage (<RET> if done): "
			     usage-names 'always nil nil)))
    (mapconcat
     (function
      (lambda (x) (format "%s" x)))
     (nreverse usages)
     "\n")))

(defun dg-install-theorem (sqn-no thm-name usage-list)
  "Install sequent SQN-NO as a theorem with name THM-NAME and usage USAGE-LIST.
The theorem is the universal closure of the implication whose consequent is the
assertion of the sequent and whose antecedent is the conjunction of the
sequent's assumptions."
  (interactive
   (list (current-sqn-no)
	 (imps-read-from-minibuffer "Theorem name: " nil inferior-tea-minibuffer-map nil)
	 (retrieve-usage-list)))
  (tea-eval-expression
   (format
    "(dg-emacs-install-theorem %d '%s '(%s))" sqn-no thm-name usage-list)))
    
(defun sqn-display-dg-chunk (sqn-no)
  (interactive (list (current-sqn-no)))
  (switch-to-buffer-other-window (dg-buffer))
  (goto-char (point-min))
  (word-search-forward (format "%s" sqn-no) (point-max) t))


(defvar imps-input-history '()
  "List of previously submitted IMPS inputs.")

(defconstant imps-input-history-max 32
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

(defun abort-resetting-history-offset ()
  "Command to abort recursive-edit, resetting IMPS history offset."
  (interactive)
  (imps-reset-history-offset)
  (abort-recursive-edit))


(defun imps-comment-latest-entry ()
  (interactive)
  (if (deduction-graph-history (current-dg))
         (set (dg-history-entry-comments 
              (car (deduction-graph-history (current-dg)))) (read-from-minibuffer "Comment: "))))


;(defun check-imps-syntax-of-expression (arg)
;  "Check syntax of an expression."
;  (interactive "p")
;  (let ((formula
;
;	 ;;Allow grabbing of expressions with mouse (if desired!)
;
;	 (let ((x-process-mouse-hook (if (and (or (featurep 'imps-x-support)
;						  (featurep 'imps-fsf-support)
;						  (featurep 'imps-lucid-support))
;					      (boundp 'expression-grabber-mouse-hook))
;					 expression-grabber-mouse-hook
;				       nil)))
;
;	   (imps-read-from-minibuffer "Formula or reference number: " nil
;				      inferior-tea-minibuffer-map))))
;    (let ((mess
;	   (get-literal-from-tea 
;	    (format "(bind (((imps-signal-error-procedure)
;                        (lambda x
;                          (ignore x)
;                            ((imps-error-continuation) \"Invalid syntax\"))))
;                          (call-with-current-continuation
;                            (lambda (kappa)
;                              (bind (((imps-error-continuation) kappa))
;                                 (qr \"%s\")  \"Valid syntax\"))))" formula))))
;      (message mess))))



    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    
