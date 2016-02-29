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

(provide 'protocols)

(defun argument-retrieval-protocol (command)
  (let ((probe (assoc command imps-commands)))
    (if probe 
	(nth 0 (cdr probe))
      'default-argument-retrieval-protocol))) 

(defvar *ui-sqn-last-value*)
(defvar *ui-sqn-last-number*)

(defun ui-sqn-last-value () *ui-sqn-last-value*)
(defun ui-sqn-last-number ()  *ui-sqn-last-number*)
(defun ui-sqn-just-one-p () (=  *ui-sqn-last-number* 1))
  
(defun ui-sqn-get (fn)
  (setq *ui-sqn-last-value*
	(get-literal-from-tea (format "(%s (sequent-unhash %d))" fn (current-sqn-no))))
  (setq *ui-sqn-last-number* (length *ui-sqn-last-value*))
  (if (= *ui-sqn-last-number* 0) (error "%s: Null list." fn)))
    
(defun ui-sqn-get-number (fn)
  (setq *ui-sqn-last-number*
	(get-literal-from-tea (format "(length (%s (sequent-unhash %d)))" fn (current-sqn-no))))
  (if (= *ui-sqn-last-number* 0) (error "%s: Null list." fn)))

(defun ui-format (format-str &rest args)
  (apply #'format (concat "(list " format-str ")") args))

(defvar *imps-minibuffer-read-history* nil)

(defun imps-read-from-minibuffer (prompt &optional initial-input keymap read history)
  (let ((history  (or history '*imps-minibuffer-read-history*)))
    (catch 'minibuffer-read-tag
      ;; I'm sorry if catches and throws are offensive to people, but it
      ;; is very convenient in this case.
      (let ((keymap (or keymap imps-minibuffer-map)))
	(read-from-minibuffer prompt initial-input keymap read history)))))

(defun read-indices-from-minibuffer (prompt &optional choices)
  (let ((x-process-mouse-hook (if (and (or (featurep 'imps-x-support)
					   (featurep 'imps-fsf-support)
					   (featurep 'imps-lucid-support))
				       (boundp 'assumption-number-mouse-hook))
				  assumption-number-mouse-hook
				nil)))
    (let ((new-prompt (if choices
			  (concat  prompt 
				   "-- ("
				   (mapconcat #'(lambda (x) (format "%d" x)) 
					      choices " ")
				   "): ")
			prompt)))
      (imps-read-from-minibuffer new-prompt nil nil nil))))

(defun read-one-index-from-minibuffer (prompt &optional choices)
  (catch 'minibuffer-read-tag

    (let ((x-process-mouse-hook (if (and (or (featurep 'imps-x-support)
					     (featurep 'imps-fsf-support)
					     (featurep 'imps-lucid-support))
					 (boundp 'assumption-number-and-exit-mouse-hook))
				    assumption-number-and-exit-mouse-hook
				  nil)))
      (let* ((new-prompt (if choices
			     (concat  prompt 
				      "-- ("
				      (mapconcat #'(lambda (x) (format "%d" x))
						 choices " ")
				      "): ")
			   prompt))
	     (index
	      (imps-read-from-minibuffer new-prompt nil nil 't)))
	(if choices (or (memq index choices) 
			(error "Index must be one of %s." choices)))
	index))))

(defun default-argument-retrieval-protocol () (ui-format ""))

(defun general-argument-retrieval-protocol ()
  (ui-format "%s" (imps-read-from-minibuffer "Command Arguments: ")))

(defun one-sequent-retrieval-protocol ()
  (ui-format "(sequent-unhash %d)"
	     (read-one-index-from-minibuffer "Major premise number: ")))

(defun cut-retrieval-protocol ()
  (ui-format "(sequent-unhash %d)"
	     (read-one-index-from-minibuffer "Major premise number: ")))

(defun imps-input-quote-string-if-needed (str)
  "Take a STRING and return \"STRING\", if not already of this form."
  (if (string-match "^\"[^\"]*\"$" str) ;;already quoted
		str
	      (format "\"%s\"" str))) 

(defun cut-with-single-formula-retrieval-protocol ()
  "Cut with FORMULA-STR."
  (let ((formula-str (imps-read-from-minibuffer "Formula to cut: ")))
    (ui-format "%s"
	    (imps-input-quote-string-if-needed formula-str))))


;;Remark: This is used only for the NSA extension.

(defun transfer-formula-retrieval-protocol ()
  "Cut with FORMULA-STR."
  (let ((formula-str
	 (imps-read-from-minibuffer "transfer-formula: ")))
    (ui-format  "%s" (imps-input-quote-string-if-needed formula-str))))

(defun formula-list-by-index-retrieval-protocol ()
  (ui-sqn-get-number 'sequent-node-assumptions)
  (ui-format "'(%s)"
	     (if (ui-sqn-just-one-p) 0
	       (read-indices-from-minibuffer "List of formulas to omit: "))))

(defun selective-antecedent-inference-rp ()
  (ui-sqn-get 'sqn-antecedent-inference-assumptions)
  (ui-format "'(%s)"
	     (if (ui-sqn-just-one-p) (car (ui-sqn-last-value))
	       (read-indices-from-minibuffer
		"List of formula indices for antecedent inferences"))))

(defun locations-in-formula-retrieval-protocol ()
  (let ((indices (imps-read-from-minibuffer "Occurrences of conditionals to be raised (0-based): "
				       "" nil nil)))
    (ui-format "'(%s)" indices)))

(defun macete-and-expressions-in-formula-retrieval-protocol ()
  (let ((macete-name (or *macete-from-menu* (read-macete)))

	(expr-str
	 (imps-read-from-minibuffer "Expression to apply macete: "))
	(indices (imps-read-from-minibuffer "Occurrences of expression (0-based): ")))
    (ui-format "'%s '(%s) %s"
	    macete-name
	    indices
	    (imps-input-quote-string-if-needed expr-str))))

(defun symbol-locations-in-formula-retrieval-protocol ()
  (ui-sqn-get 'defined-constants-in-assertion)
  (let* ((constant
	  (if (ui-sqn-just-one-p)
	      (car (car (ui-sqn-last-value)))
	    (completing-read-or-get-from-x-menu 
	     "Constant name: " (ui-sqn-last-value) nil nil nil)))
	 
	 (positions (cdr (assoc constant (ui-sqn-last-value))))
	  
	 (indices (if (= (length positions) 1)
		      "0"
		    (imps-read-from-minibuffer "Occurrences to unfold (0-based): "
						"" nil nil))))
    (ui-format "'(%s) '%s" indices constant)))

(defvar *macete-from-menu* nil)

(defun macete-retrieval-protocol ()
  (ui-format "'%s" (or *macete-from-menu* (read-macete))))

(defun theorem-retrieval-protocol ()
  (ui-format "'%s" (imps-read-from-minibuffer "Theorem name: ")))

(defun force-substitution-retrieval-protocol ();;(target-str replacement-str occurrence)
  "Force REPLACEMENT-STR to replace TARGET-STR at the OCCURRENCE'th occurrence."
  (let ((target-str
	 (imps-read-from-minibuffer "Expression to replace: " nil nil nil))
	(replacement-str
	 (imps-read-from-minibuffer "Replace it with: " nil nil nil))
	(occurrences
	 (imps-read-from-minibuffer "0-based indices of occurrences to change: " nil nil nil)))
    (ui-format "%s %s '(%s)" 
	    (imps-input-quote-string-if-needed target-str)
	    (imps-input-quote-string-if-needed replacement-str)
	    occurrences)))

(defun single-formula-retrieval-protocol ()
  (ui-sqn-get-number 'sequent-node-assumptions)
  (ui-format "(nth (sequent-node-assumptions (sequent-unhash %d)) %d)"
	     (current-sqn-no)
	     (if (ui-sqn-just-one-p) 0
	       (read-one-index-from-minibuffer "0-based index of antecedent-formula: "))))

(defun existential-formula-and-variables-retrieval-protocol ()
  (let ((formula-index
	 (read-indices-from-minibuffer "0-based index of existential formula: " ))
	(variable-strs (collect-a-bunch-of-variables)))
    (ui-format "'%s '(%s)" formula-index variable-strs)))

(defun one-sequent-argument-retrieval-protocol ()
  (ui-format "(sequent-unhash %d)"
	     (read-one-index-from-minibuffer "Auxiliary sequent number: ")))

(defun collect-a-bunch-of-variable-instantiations (variable-sorts)
  (let (terms new-string)
    (while variable-sorts
      (setq
       new-string
       (imps-read-from-minibuffer
	(format "%s%s%s%s: "
		"Instance for variable " (car variable-sorts)
		" of sort " (car (cdr variable-sorts)))
	nil nil nil))
      (setq terms (cons new-string terms))
      (setq variable-sorts (cdr (cdr variable-sorts))))
    (mapconcat (function
		(lambda (x) (format "%s" (imps-input-quote-string-if-needed x))))
	       (nreverse terms) "\n")))

(defun collect-a-bunch-of-terms ()
  (let (terms new-string)
    (setq new-string
	  (imps-read-from-minibuffer "First instance term: " nil nil nil))
    (while (not (string= "" new-string))
      (setq terms (cons new-string terms))
      (setq new-string (imps-read-from-minibuffer
			"Next instance term (<RET> if done): " nil nil nil)))
    (mapconcat (function
		(lambda (x) (format "%s" (imps-input-quote-string-if-needed x))))
	       (nreverse terms) "\n")))

(defun collect-a-bunch-of-variables ()
  (let (variables new-string)
    (setq new-string
	  (imps-read-from-minibuffer "First variable: " nil nil nil))
    (while (not (string= "" new-string))
      (setq variables (cons new-string variables))
      (setq new-string (imps-read-from-minibuffer
			"Next variable (<RET> if done): " nil nil nil)))
    (mapconcat (function
		(lambda (x) (format "%s" (imps-input-quote-string-if-needed x))))
	       (nreverse variables) "\n")))

(defun collect-a-bunch-of-formulas ()
  (let (terms new-string)
    (setq new-string
	  (imps-read-from-minibuffer "First formula: " nil nil nil))
    (while (not (string= "" new-string))
      (setq terms (cons new-string terms))
      (setq new-string (imps-read-from-minibuffer
			"Next formula (<RET> if done): " nil nil nil)))
    (mapconcat (function
		(lambda (x) (format "%s" (imps-input-quote-string-if-needed x))))
	       (nreverse terms) "\n")))

;;will define 
;;(defun menu-invoked-p () 
;;   (and (boundp 'imps-mouse-call-p) imps-mouse-call-p))
;; This is redefined ins imps-fsf-support.

(defun request-induction-variable (induction-var-sorts)
  (if (= (length induction-var-sorts) 1)
      (format "%s" (imps-input-quote-string-if-needed (car (car induction-var-sorts))))
    (let* ((prompt-string
	    (if (and (boundp 'imps-mouse-call-p) imps-mouse-call-p)
		"Variable to induct on:"
	      "Variable to induct on (<RET> to use IMPS default): "))
	   (induction-var-sorts
	    (if (and (boundp 'imps-mouse-call-p) imps-mouse-call-p)
		(cons '("Use IMPS default.") induction-var-sorts)
	      induction-var-sorts))
	   (term-string
	    (completing-read-or-get-from-x-menu prompt-string induction-var-sorts nil nil nil)))
      (if (or (string= "" term-string)
	      (string= "Use IMPS default." term-string))
	  ""
	
	(format "%s" (imps-input-quote-string-if-needed term-string))))))

(defun theorem-instantiation-retrieval-protocol ()
  (let ((thm-name
	 (imps-read-from-minibuffer "Theorem name: ")))
    (let ((var-sorts (imps-get-theorem-var-sorts thm-name)))
      (ui-format "'%s '(%s)"  
	      thm-name
	      (collect-a-bunch-of-variable-instantiations var-sorts)))))

(defun instantiate-existential-retrieval-protocol ()
  (ui-sqn-get 'sqn-existential-with-variable-sorts)
  (ui-format "'(%s)" (collect-a-bunch-of-variable-instantiations (ui-sqn-last-value))))

(defun case-split-retrieval-protocol ()
  (ui-format "'(%s)" (collect-a-bunch-of-formulas)))

(defun instantiate-universal-retrieval-protocol ()
  (ui-sqn-get 'sqn-univeral-assumptions-with-variable-sorts)
  
  (if (ui-sqn-just-one-p)
      (ui-format "(nth (sequent-node-assumptions (sequent-unhash %d)) %d) '(%s)"
		 (current-sqn-no)
		 (car (car (ui-sqn-last-value)))
		 (collect-a-bunch-of-variable-instantiations (cdr (car (ui-sqn-last-value)))))
    (let* ((indices (mapcar 'car (ui-sqn-last-value)))
		    
	   (index
	    (read-one-index-from-minibuffer
	     "0-based index of universal antecedent formula"
	     indices))
	   (variable-sorts (cdr (assoc index (ui-sqn-last-value)))))

      (ui-format
       "(nth (sequent-node-assumptions (sequent-unhash %d)) %d) '(%s)"
       (current-sqn-no)
       index
       (collect-a-bunch-of-variable-instantiations variable-sorts)))))




(defun single-universal-formula-retrieval-protocol ()
  (ui-sqn-get 'sqn-univeral-assumptions-with-variable-sorts)
  (ui-format
   "(nth (sequent-node-assumptions (sequent-unhash %d)) %d)"
   (current-sqn-no)
   (if (ui-sqn-just-one-p) (car (ui-sqn-last-value))
     (read-one-index-from-minibuffer
      "0-based index of universal antecedent formula"
      (ui-sqn-last-value)))))
		  

(defun instantiate-universal-multiply-retrieval-protocol ()
  (let ((index (read-indices-from-minibuffer "0-based index of antecedent-formula: "))
	(terms-s (list (collect-a-bunch-of-terms))))
    (while (y-or-n-p "Input terms for another instance? ")
      (setq terms-s (cons (collect-a-bunch-of-terms) terms-s)))
    (ui-format "'%s '((%s))"  
	    index
	    (mapconcat (function
			(lambda (x) (format "%s" x)))
		       (nreverse terms-s) ")\n("))))

(defun antececent-formula-retrieval-protocol ()
  (ui-format "'%s" (read-one-index-from-minibuffer "0-based index of antecedent-formula: ")))

(defun antececent-inference-retrieval-protocol ()
  (ui-sqn-get 'sqn-antecedent-inference-assumptions)
  (ui-format
   "(nth (sequent-node-assumptions (sequent-unhash %d)) %d)"
   (current-sqn-no)
   (if (ui-sqn-just-one-p) (car (ui-sqn-last-value))
     (read-one-index-from-minibuffer
      "0-based index of antecedent formula"
      (ui-sqn-last-value)))))

(defun repeated-backchain-rp ()
  (ui-sqn-get 'sqn-backchain-inference-assumptions)      
  (ui-format
   "(choose-list-entries (sequent-node-assumptions (sequent-unhash %d)) '(%s))"
   (current-sqn-no)
   (if (ui-sqn-just-one-p) (car (ui-sqn-last-value))
     (read-indices-from-minibuffer
        "0-based index of antecedent formulas"
	(ui-sqn-last-value)))))

(defun backchain-inference-rp ()
  (ui-sqn-get 'sqn-backchain-inference-assumptions)
  (ui-format
   "(nth (sequent-node-assumptions (sequent-unhash %d)) %d)"
   (current-sqn-no)
   (if (ui-sqn-just-one-p) (car (ui-sqn-last-value))
     (read-one-index-from-minibuffer
      "0-based index of antecedent formula"
      (ui-sqn-last-value)))))

(defun backchain-backwards-inference-rp ()
  (ui-sqn-get 'sqn-backchain-backwards-inference-assumptions)      
  (ui-format
   "(nth (sequent-node-assumptions (sequent-unhash %d)) %d)"
   (current-sqn-no)
   (if (ui-sqn-just-one-p) (car (ui-sqn-last-value))
     (read-one-index-from-minibuffer
      "0-based index of antecedent formula"
      (ui-sqn-last-value)))))


(defun force-substitution-at-occurrences-retrieval-protocol ();;(target-str replacement-str occurrence)
  "Force REPLACEMENT-STR to replace TARGET-STR at the OCCURRENCE'th occurrence."
  (let ((target-str
	 (imps-read-from-minibuffer "Expression to replace: " nil nil nil))
	(replacement-str
	 (imps-read-from-minibuffer "Replace it with: " nil nil nil))
	(occurrences
	 (imps-read-from-minibuffer "0-based indices of occurrences to change: " "()" nil t)))
    (ui-format "%s %s '%s"
	    (imps-input-quote-string-if-needed target-str)
	    (imps-input-quote-string-if-needed replacement-str)
	    occurrences)))

(defun simplify-antecedent-retrieval-protocol ()
  (ui-format "(nth (sequent-node-assumptions (sequent-unhash %d)) %d)"
	     (current-sqn-no)
	     (read-one-index-from-minibuffer "0-based index of antecedent-formula: ")))

(defun induction-arguments-retrieval-protocol ()
  (ui-sqn-get 'determine-applicable-inductors)
  (let ((inductor
	 (if (ui-sqn-just-one-p) (car (car (ui-sqn-last-value)))
	   (completing-read-or-get-from-x-menu "Inductor: " (ui-sqn-last-value) nil nil nil))))
    (ui-format "'%s '(%s)" 
	       inductor
	       (request-induction-variable (cdr (assoc inductor (ui-sqn-last-value)))))))

(defun instantiate-transported-theorem-retrieval-protocol ()
  "Add to the context of SQN the instance of the translation of THM-NAME under 
   TRANSLATION-NAME in which the universally quantified variables are replaced by 
   TERM-STRINGS. "
  (let ((theorem-name (imps-read-from-minibuffer "Theorem name: "))
	(translation-name
	 (imps-read-from-minibuffer "Theory interpretation (<RET> to let IMPS find one): ")))
    (let ((var-sorts (imps-get-theorem-var-sorts theorem-name)))
      (if (string= "" translation-name)
	  (ui-format "'%s '() '(%s)"
		  theorem-name
		  (collect-a-bunch-of-variable-instantiations var-sorts))
	(ui-format "'%s '%s '(%s)" 
		   theorem-name 
		   translation-name
		   (collect-a-bunch-of-variable-instantiations var-sorts))))))

(defun symbol-retrieval-protocol ()
  (ui-sqn-get 'defined-constants-in-assertion)
  (let ((constant
	 (if (ui-sqn-just-one-p)
	     (car (car (ui-sqn-last-value)))
	   (completing-read-or-get-from-x-menu 
	    "Constant name: " 
	    (ui-sqn-last-value)  nil nil nil))))
    (ui-format "'%s" constant)))

(defun disable-quasi-constructor-retrieval-protocol ()
  (ui-sqn-get 'quasi-constructors-in-sequent)
  (ui-format "'%s" 
	     (completing-read-or-get-from-x-menu 
	      "Quasi-constructor name: " (ui-sqn-last-value) nil nil nil)))

(defun enable-quasi-constructor-retrieval-protocol ()
  (ui-sqn-get 'disabled-quasi-constructors)
  (ui-format "'%s" 
	     (completing-read-or-get-from-x-menu 
	      "Quasi-constructor name: " (ui-sqn-last-value) nil nil nil)))

;;; (defun fixpoint-induction-rp ()
;;;   (let* ((pred-symbol (imps-read-from-minibuffer "Recursive predicate name: " "" nil t))
;;; 	 (term-string
;;; 	  (imps-read-from-minibuffer
;;; 	   "Predicate of induction (<RET> to use IMPS default): " nil nil nil)))
;;;     (if (string= "" term-string)   
;;; 	(format "(list '%s '())" pred-symbol)
;;;       (format "(list '%s \"%s\")" pred-symbol term-string))))

(defun single-equation-retrieval-protocol ()
  (ui-format "\"%s\"" (imps-read-from-minibuffer "Equality: " "" nil nil)))

(defun single-equation-or-inequality-retrieval-protocol ()
  (ui-format "\"%s\"" (imps-read-from-minibuffer "Inequality or equality: " "" nil nil)))

(defun persistence-request-retrieval-protocol ()
  (ui-format "%d" 
	  (imps-read-from-minibuffer "Backchaining persistence: " "0" nil t)))

(defun definition-names-retrieval-protocol ()
   (ui-format "'(%s)"
	      (imps-read-from-minibuffer "Definition names to use: "  nil nil nil)))


(defun sequent-edit-and-post-retrieval-protocol ()
  "Put current sqn into a buffer to edit.    "
  (interactive)
  (sqn-edit-sqn current-prefix-arg)
  (throw 'apply-command-tag nil))


(defun assume-transported-theorem-retrieval-protocol ()
  "Add to the context of SQN the translation of THM-NAME under TRANSLATION-NAME."
  (let ((theorem-name (imps-read-from-minibuffer "Theorem name: "))
	(translation-name
	 (imps-read-from-minibuffer "Translation name: ")))
    (let ((var-sorts (imps-get-theorem-var-sorts theorem-name)))
      (ui-format "'%s '%s" theorem-name translation-name))))


(defun eliminate-defined-iota-expression-retrieval-protocol ()
  (let ((iota-expr-index 
	 (imps-read-from-minibuffer 
	  "0-based index of iota expression occurrence: " "0" nil t))
	(new-variable-name
	 (imps-read-from-minibuffer 
	  "Name of replacement variable: " nil nil nil)))
    (ui-format "'%s '%s" iota-expr-index new-variable-name)))

(defun eliminate-iota-retrieval-protocol ()
  (let ((iota-expr-index 
	 (imps-read-from-minibuffer 
	  "0-based index of iota expression occurrence: " "0" nil t)))
    (ui-format "'%s" iota-expr-index)))

(defun informal-justification-retrieval-protocol ()
  (let ((j-str (imps-read-from-minibuffer "State justification: ")))
    (ui-format "%s" (imps-input-quote-string-if-needed j-str))))

(defconst *max-menu-size* 40)

(or (fboundp 'completing-read-or-get-from-x-menu)
    (defun completing-read-or-get-from-x-menu (prompt table predicate
						      require-match initial-input)
      (if (and (featurep 'imps-x-support)
	       (boundp 'imps-mouse-call-p)
	       imps-mouse-call-p
	       (listp table)
	       (<= (length table) *max-menu-size*))
	  (let ((string (imps-popup-menu
			 '(0 0)
			 (list "Menu"
			       (cons (replace-chars-in-string prompt 58 32)
				     (mapcar
				      '(lambda (x)
					 (cons x x))
				      (mapcar 'car table)))))))
	    (if string string (error "Command aborted.")))
	(completing-read prompt table predicate require-match initial-input))))


(defun imps-display-entries (&optional sqn-no)
  (interactive)
  (let ((config (current-window-configuration))
	(buffer (get-buffer-create "*Context-Entries*"))
	(num (if sqn-no sqn-no
	       (car (read-from-string (format "%d" (current-sqn-no)))))))
    (let ((entries
	   (get-literal-from-tea
	    (format "(with-output-to-string p
                 (context-walk-entries
                    (lambda (s) (format p \"~A~%%~%%\" (qp s)))
                    (sequent-node-context (sequent-unhash %d ))))" num))))
      (set-buffer buffer)
      (setq buffer-read-only nil)
      (pop-to-buffer buffer)
      (erase-buffer)
      (goto-char (point-min))
      (insert entries)
      (setq buffer-read-only t))))

(defun annotate-protocol ()
  (let ((keyword
	 (completing-read-or-get-from-x-menu
	  "Keyword: " '(("begin-block")("end-block")) nil nil "begin-block")))
    (ui-format "'%s" keyword)))

(defun bnf-take-cases-protocol ()
  (let ((axiom-name
	 (get-literal-from-tea
	  (format
	   "(bnf-sortname->case-axiom-name '%s '%s)"
	   (imps-read-from-minibuffer "Bnf name: ")
	   (imps-read-from-minibuffer "Sort name: ")))))
    (let ((var-sorts (imps-get-theorem-var-sorts axiom-name)))
      (format "(list '%s '(%s))"  
	      axiom-name
	      (collect-a-bunch-of-variable-instantiations var-sorts)))))



;;;Argument transmission  (from EMACS to TEA)
 
(defun transmit-command-and-args (command sqn-nos aux-args)
  (tea-eval-large-expression-and-update-sqn-and-dg
     (format
      "(deduction-graph-apply-command-interface (current-dg) '%s '%s %s '())"
      command sqn-nos aux-args)))


    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    
