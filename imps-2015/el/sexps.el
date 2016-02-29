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



(provide 'sexps)

(defun string-char-pos (string char &optional count)
  "If STRING contains CHAR, return its index.  Optional COUNT 
is a repeat count."
  (let ((index -1)
	(bound (1- (length string)))
	(count (or count 1)))
    (while (and (> count 0)
		(< index bound))
      (setq index (1+ index))
      (if (char-equal (aref string index) char)
	  (setq count (1- count))))
    (if (zerop count)
	index
      nil)))

(defun string-char-pos-after (string char start)
  "If STRING contains CHAR after START, return its index.  "
  (let ((index start)
	(bound (1- (length string))))
    (while (and (< index bound)
		(not (char-equal (aref string index) char)))
      (setq index (1+ index)))
    (if (< index bound) index)))


(defun string-char-pos-list (string char)
  "Return list of all indices in STRING where CHAR occurs."
  (let ((index -1)
	(bound (1- (length string)))
	index-list)
    (while (< index bound)
      (setq index (1+ index))
      (if (char-equal (aref string index) char)
	  (setq index-list (cons index index-list))))
    (nreverse index-list)))

(defun string-char-last-pos (string char)
  "If STRING contains CHAR, return its last index, as a negative offset from end."  
  (let ((i (1- (length string)))
	(found nil))
    (while (and (>= i 0)
		(not found))
      (if (char-equal (aref string i) char)
	  (setq found t)
	(setq i (1- i))))
    (if found i nil)))

(defun subst-char-in-string (string from-char to-char)
  "Modify STRING by replacing FROM-CHAR with TO-CHAR throughout."
  (let ((index 0)
	(len (length string)))    
    (while (< index len)
      (if (char-equal from-char (aref string index))
	  (aset string index to-char))
      (setq index (1+ index)))
    string))

(defun cheap-looking-at (syntax-code-list)
  "t iff char-after point has syntax code in SYNTAX-CODE-LIST."
  (char-syntax-in (char-after (point)) syntax-code-list))
		
(defun char-syntax-in (char syntax-code-list)
  "t iff CHAR has syntax code in SYNTAX-CODE-LIST."
  (and (numberp char)
       (memq
	 (char-syntax char)
	 syntax-code-list)))

(defun skip-by-syntax (syntax-code-list &optional lim)
  "Move point forward, stopping before a char with syntax not in syntax-code-list, or at position LIM. 
Returns t iff reaches a char with different syntax."
  (let ((lim (or lim (1- (point-max)))))
    (while (and (< (point) lim)
		(cheap-looking-at syntax-code-list))
      (forward-char 1))
    (not (cheap-looking-at syntax-code-list))))


(defun string-skip-by-syntax (string start-index syntax-code-list &optional lim)
  "Return position in STRING containing a char with syntax not in SYNTAX-CODE-LIST, 
if before position LIM, otherwise nil."
  (let ((lim (or lim (length string)))
	(index start-index))
    (while (and (< index lim)
		(memq
		 (char-syntax (aref string index))
		 syntax-code-list))
      (setq index (1+ index)))
    (and (< index lim) index)))
    

(defconst symbol-syntax '(?w ?_)) 
(defconst opener-syntax '(?\())
(defconst closer-syntax '(?\)))
(defconst whitespace-syntax '(?  ?>))

(defun beginning-of-symbol (pos)
  "Move to beginning of symbol including or after POS."
  (interactive "d")
  (goto-char pos)
  (if (cheap-looking-at symbol-syntax)
      (progn (forward-char 1)
	     (backward-sexp 1))
    (while (not (or (eobp)
		    (cheap-looking-at symbol-syntax)))
      (forward-char 1))))

(defun next-symbol-start (pos)
  "Return the start location of the next symbol including or after POS."
  (save-excursion
    (beginning-of-symbol pos)
    (point)))

(defun next-symbol-boundaries (pos)
  "Return the start and end locations (as pair) of the next symbol including or after POS."
  (save-excursion
    (beginning-of-symbol pos)
    (let ((start (point)))
      (forward-sexp 1)
      (cons start (point)))))

(defun next-symbol-end (pos)
  "Return the end location of the next symbol including or after POS."
  (cdr (next-symbol-boundaries pos)))

(defun next-symbol-string (pos)
  "Return the string of characters including or after POS making up the next symbol."
  (let ((p (next-symbol-boundaries pos)))
    (buffer-substring (car p) (cdr p))))
   
(defun pos-within-symbol-p (pos)
  "t iff pos is within a symbol."
  (char-syntax-in (char-after pos) symbol-syntax))

(defun integers-within-region (start end)
  "return a list of all integers printed within region START to END."
  (let ((ints nil))
    (save-excursion
      (save-restriction
	(narrow-to-region start end)
	(goto-char (point-min))
	(while (not (eobp))
	  (beginning-of-symbol (point))
	  (let* ((bounds (next-symbol-boundaries (point)))
		 (next
		  (condition-case tmp
		      (read (buffer-substring (car bounds) (cdr bounds)))
		    (error nil))))
	    (if (integerp next)
		(setq ints (cons next ints)))
	    (goto-char (cdr bounds))))
	ints))))

(defun case-fold-string= (str1 str2)
  "t iff STR1 and STR2 are the same, ignoring case."
  (let ((d1 (downcase str1))
	(d2 (downcase str2)))
    (string= d1 d2)))

(defun string-mem (str lst)
  "Like MEM, but for lists of strings.
Comparison done with (lambda (s1 s2) (and (stringp s2) (string= s1 s2)))." 
  (while (and lst
	      (or (not (stringp (car lst)))
		  (not (string= str (car lst)))))
    (setq lst (cdr lst)))
    lst)

(defun list-next-p (pos)
  "t iff a list begins before the next symbol or list-end after POS."
  (save-excursion
    (goto-char pos)
    (while (not (or (cheap-looking-at opener-syntax)
		    (cheap-looking-at closer-syntax)
		    (cheap-looking-at symbol-syntax)))
      (forward-char 1)) 
    (cheap-looking-at opener-syntax)))

(defun next-null-item (pos)
  "Return starting point of next null list item, and nil if there is none.  
A null list item is an openers followed be blanks and linefeeds and ultimately
a closer."  
  (save-excursion
    (goto-char pos)
    (if (re-search-forward "\\s(\\(\\s \\|\\s>\\)*\\s)" nil t)
	(cons (match-beginning 0)
	      (match-end 0))
      nil)))

(defun up-closers ()
  "Move (forward) up list structure past close-parens of any sort, whitespace, and linefeeds."
  (let ((last-closer (point)))
    (while (or (cheap-looking-at whitespace-syntax)
	       (cheap-looking-at closer-syntax))
      (if (cheap-looking-at closer-syntax)
	  (setq last-closer (point)))
      (forward-char 1))
    (goto-char (1+ last-closer))))

(defun up-openers ()
  "Move (backward) up list structure past open-parens of any sort, whitespace, and linefeeds."
  (interactive)
  (let ((last-opener (point)))
    (while (and (not (bobp))
		(progn (backward-char 1)
		       (or (cheap-looking-at whitespace-syntax)
			   (cheap-looking-at opener-syntax))))
      (if (cheap-looking-at opener-syntax)
	  (setq last-opener (point))))
    (goto-char last-opener)))

(defun down-openers ()
  "Move (forward) down list structure past open-parens of any sort, whitespace, and linefeeds."
  (let ((last-opener (point)))
    (while (or (cheap-looking-at whitespace-syntax)
	       (cheap-looking-at opener-syntax))
      (if (cheap-looking-at opener-syntax)
	  (setq last-opener (point)))
      (forward-char 1))
    (goto-char (1+ last-opener))))

(defun down-closers ()
  "Move (backward) down list structure past close-parens of any sort, whitespace, and linefeeds."
  (let ((last-closer (point)))
    (while (and (not (bobp))
		(progn (backward-char 1)
		       (or (cheap-looking-at whitespace-syntax)
			   (cheap-looking-at closer-syntax))))
      (if (cheap-looking-at closer-syntax)
	  (setq last-closer (point))))
    (goto-char last-closer)))

(defun next-sexp-boundaries (pos)
  "Pair of character numbers at which the sexp after or immediately enclosing POS begins and ends."
  (let ((end (or (scan-sexps pos 1) pos)))
    (cons (or (scan-sexps end -1) pos)
	  end)))

(defun next-sexp-start (pos)
  "Character numbers at which the sexp after or immediately enclosing POS begins."
  (car (next-sexp-boundaries pos)))

(defun next-sexp-end (pos)
  "Character numbers at which the sexp after or immediately enclosing POS ends."
  (cdr (next-sexp-boundaries pos)))

(defun beginning-of-enclosing-list ()
  "Move point to beginning of first item in list immediately enclosing current point."
  (interactive)
  (up-list -1)
  (down-list 1))

;; (defun last-list-item-p (pos)
;;   "t iff POS lies in (or at end of) the last item in its immediately enclosing list."
;;   (save-excursion
;;     (if (pos-within-symbol-p pos)
;; 	(goto-char (next-symbol-end pos)))
;;     (let ((here (point)))
;;       (up-closers)
;;       (> (point) here))))

(defun last-list-item-p (pos)
  "t iff POS lies in (or at end of) the last item in its immediately enclosing list."
  (save-excursion
    (let ((pos
	   (if (pos-within-symbol-p pos)
	       (next-symbol-end pos)
	     pos)))
      (not
       (condition-case tmp
	   (scan-sexps pos 1)
	 (error nil))))))

(defun first-list-item-p (pos)
  "t iff POS lies in (or at beginning of) the first item in an immediately enclosing list."
  (save-excursion
    (if (pos-within-symbol-p pos)
	(goto-char (next-symbol-start pos)))
    (let ((here (point)))
      (up-openers)
      (< (point) here))))

(defun start-of-indexed-list-item (i)
  "Return start of the ith item in the closest enclosing list (zero-based)."
  (save-excursion
    (up-list -1)
    (down-list 1)
    (forward-sexp i)
    (next-sexp-start (point))))

(defun end-of-whitespace (start)
  (save-excursion
    (goto-char start)
    (while (cheap-looking-at whitespace-syntax)
      (forward-char 1))
    (point)))

(defun balance-defuns (buff)
  "Check that every defun in BUFF is balanced (current-buffer if interactive)."
  (interactive (list (current-buffer)))
  (set-buffer buff)
  (let ((next-end (point-min)))
    (condition-case ddd
	(progn
	  (while (setq next-end (scan-lists next-end 1 0)))
	  (if (interactive-p)
	      (message "All defuns balanced.")
	    t))
      (error
       (push-mark nil t)
       (goto-char next-end)
       (cond ((interactive-p)
	      (ding)	      
	      (message "Unbalanced defun."))
	     (t nil))))))

(defun string-defuns-balanced-p (str)
  "True if all parentheses in STR are properly balanced."
  (let ((tmp (get-buffer-create " tmp")))
    (set-buffer tmp)
    (erase-buffer)
    (insert str)
    (balance-defuns tmp)))
    

(put 'unbalanced-defun 'error-conditions '(error unbalanced-defun))
(put 'unbalanced-defun 'error-message "Unbalanced defun")

(defun balance-defun-hook ()
  (cond ((or current-prefix-arg
	     (balance-defuns (current-buffer)))
	 nil) 
	((interactive-p)
	 (error "Unbalanced defun -- buffer not saved.  Prefix arg to force save."))
	(t
	 (signal 'unbalanced-defun
		 '("buffer not saved -- Prefix arg to force save")))))

(defun balance-defuns-and-save (force)
  "Call  balance-defuns  on current-buffer and save it if all defuns are balanced. 
Prefix arg means force save without checking for balance."
  (interactive "P")
  (if (or force (balance-defuns (current-buffer)))
      (save-buffer)
    (ding)
    (message "Unbalanced defun -- buffer not saved.")))

(defun begin-next-defun ()
  (interactive)
  (cond ((re-search-forward "^\\s(" nil t 1)
	 (beginning-of-line)
	 t)
	(t nil)))

;;;(defun collect-operations (start end)
;;;  (save-excursion
;;;    (goto-char (point-min))
;;;    (let ((case-fold-search t)
;;;	  operations
;;;	  settable-operations)
;;;	 (while (search-forward "object" (point-max) t)
;;;	(if (not (case-fold-string=
;;;		  "object" (next-symbol-string (match-beginning 0))))
;;;	    nil				;;bogus match
;;;	  (forward-sexp 1)		;;skip procedure
;;;	  (while (and (list-next-p (point))
;;;		      (collect-operations-1))
;;;	    (forward-sexp 1))))
;;;	 (list operations settable-operations))))
;;;
;;;(defun collect-operations-1 ()
;;;  (save-excursion
;;;    (cond ((and
;;;	    (list-next-p (point)) (not (down-list 1))
;;;	    (list-next-p (point)) (not (down-list 1)))
;;;	   (let ((lst 
;;;		  (if (and (list-next-p (point))
;;;			   (case-fold-string= (next-symbol-string (point))
;;;					      "setter"))
;;;		      'settable-operations
;;;		    'operations))
;;;		 (name (save-excursion
;;;			 (forward-sexp 1)
;;;			 (backward-word 1)
;;;			 (downcase (next-symbol-string (point))))))
;;;	     (or (string-mem name (eval lst))
;;;		 (set lst (cons name (eval lst))))
;;;	     t))
;;;	  (t nil))))
;;;		     
;;;(defun check-operation-definitions (buff)
;;;  (interactive "bOperations in buffer: ")
;;;  (set-buffer buff)
;;;  (let* ((bops (collect-operations (point-min)(point-max)))
;;;	 (ops (car bops))
;;;	 (settable-ops (car (cdr bops)))
;;;	 (unwashed nil))
;;;    (while ops
;;;	 (or 
;;;	  (check-op-def-1 (car ops) (string-mem (car ops) settable-ops))
;;;	  (setq unwashed
;;;	     (cons (car ops) unwashed)))
;;;	 (setq ops (cdr ops)))
;;;    (if (interactive-p)
;;;	(with-output-to-temp-buffer "*Unwashed-operations*"
;;;	  (princ "Operations not defined in this buffer (or not defined as settable, but set) are:\n")
;;;	  (print unwashed))
;;;	 unwashed)))
;;;
;;;(defun check-op-def-1 (op-name settable-flag)
;;;  (save-excursion
;;;    (goto-char (point-min))
;;;    (let ((case-fold-search t)
;;;	  (def-regexp
;;;	    (if settable-flag
;;;		"(define-settable-operation\\(\\s \\|\\s>\\)+"
;;;	      "define-\\(\\(operation\\)\\|\\(predicate\\)\\)\\(\\s \\|\\s>\\)+")))
;;;	 (re-search-forward (concat def-regexp "(?" op-name) (point-max) t))))

(defun upcase-procedure-name (pos arg)
  (interactive "d\np")
  (save-excursion
    (goto-char pos)
    (let ((case-fold-search nil))
      (upcase-procedure-name-aux (and (not (= arg 0)) arg)))))

(defun upcase-procedure-name-aux (arg)
  (cond ((re-search-forward "^(def" (point-max) t)
	 (forward-sexp 1)
	 (if (list-next-p (point))
	     (down-list 1))
	 (let ((boundaries (next-sexp-boundaries (point))))
	   (upcase-region (car boundaries) (cdr boundaries))
	   (goto-char (cdr boundaries))
	   (if (and arg (<= arg 1))
	       nil
	     (upcase-procedure-name-aux (and arg (1- arg))))))
	(t nil)))
	      
(defun current-line-number ()
  "Return the current line number (in the buffer) of point."
  (interactive)
  (save-restriction
    (widen)
    (save-excursion
      (beginning-of-line)
      (1+ (count-lines 1 (point))))))

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    
