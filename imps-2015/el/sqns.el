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


;;; Support for *Sequent Nodes* and *Deduction* buffers to display the sequent
;;; nodes of a deduction-graph.

;;;(require 'process-filter)
(provide 'sqns)

(defvar sqn-display-hook nil)

(defvar current-dgr nil)

(defun make-sqn ()
  (make-vector 4 nil))

(defun sqn-start (sqn)
  (aref sqn 0))

(defun sqn-end (sqn)
  (aref sqn 1))

(defun sqn-index (sqn)
  (aref sqn 2))
(defun sqn-grounded-p (sqn)
  (aref sqn 3))

(defun sqn-set-start (sqn new-value)
  (aset sqn 0 new-value))
(defun sqn-set-end (sqn new-value)
  (aset sqn 1 new-value))
(defun sqn-set-index (sqn new-value)
  (aset sqn 2 new-value))
(defun sqn-set-grounded-p (sqn new-value)
  (aset sqn 3 new-value))

;;; A DGR, or deduction graph record, stores all the information about the state
;;; of a particular deduction graph and the sequents it contains.  

(defun make-dgr (sqn-b dg-b theory-name)
  (let ((vec (make-vector 8 nil)))
    (aset vec 0 nil)
    (aset vec 1 nil)			;the index of the current sqn in sqn-vector 
    (aset vec 2 sqn-b)			;the sqn-buffer
    (aset vec 3 dg-b)			;the dg-buffer

    (aset vec 5 theory-name)		;the name of the theory
    (aset vec 6 nil)			;the index of the last-inspected sqn
					;in sqn-vector 
    vec))

(defun dgr-sqns ()
  (aref current-dgr 0))
(defun dgr-current-sqn ()
  (aref current-dgr 1))
(defun dgr-sqn-buffer ()
  (aref current-dgr 2))
(defun dgr-dg-buffer ()
  (aref current-dgr 3))
(defun dgr-theory-name ()
  (aref current-dgr 5))
(defun dgr-last-seen-sqn ()
  (aref current-dgr 6))

(defun dgr-size ()
  (length (dgr-sqns)))

;;;(defun dgr-index-location (index)
;;;  (cdr (assoc index (aref current-dgr 7))))
;;;
;;;(defun dgr-add-location (index)
;;;  (aset current-dgr 7 (cons 
;;;		       (cons index (length (aref current-dgr 7)))
;;;		       (aref current-dgr 7))))

(defun dgr-sqns-adjoin (sqn)
  (aset current-dgr 0 (cons sqn (aref current-dgr 0))))

(defun dgr-set-current-sqn (new-index)
  (aset current-dgr 1 new-index))

;;;(error "dgr-set-current-sqn: index %d bigger than max %d."
;;;	   new-index
;;;	   (dgr-size))))

(defun dgr-set-last-seen-sqn (new-index)
  (aset current-dgr 6 new-index))

(defun clean-slate (&rest buffs)
  (mapc #'(lambda (bf) 
	    (set-buffer  bf)
	    (let ((buffer-read-only nil))
	      (erase-buffer)))
	buffs))

(defun initialize-dgr (sqn-b-name dg-b-name theory-name)
  (let ((sqn-b (get-buffer-create sqn-b-name))
	(dg-b (get-buffer-create dg-b-name)))
    (clean-slate sqn-b dg-b)
    (setq current-dgr (make-dgr sqn-b dg-b theory-name))))

(defun pop-to-buffer-tl (buff-name)
  (pop-to-buffer buff-name)
  (top-level))

(defun char-no->index (char-no)
  (let ((sqns (dgr-sqns))
	 (found '()))
    (while (and sqns (not found))
      (let ((sqn (car sqns)))
	(if (and (<= (marker-position (sqn-start sqn)) char-no)
		 (<= char-no (marker-position (sqn-end sqn))))
	    (setq found sqn))
	  (setq sqns (cdr sqns))))
    (and found (sqn-index found))))

(defun sqn-set-current-sqn (new-value)
  (dgr-set-last-seen-sqn (dgr-current-sqn))
  (dgr-set-current-sqn new-value))

(defun sqn-make-grounded (index)
  (let ((sqn (sqn-find index)))
    (if sqn
	(sqn-set-grounded-p sqn t)
      (error "sqn-make-grounded: Bad index %d" index))))

(defun sqn-find (index)
  (let ((sqns (dgr-sqns))
	(found '()))
    (while (and sqns (not found))
      (let ((sqn (car sqns)))
	(if (= (sqn-index sqn) index)
	    (setq found sqn))
	(setq sqns (cdr sqns))))
    found))


(defun sqn-display (index)
  (let ((sqn-buffer (dgr-sqn-buffer))
	(sqns (dgr-sqns)))
    (cond ((not (numberp index))
	   (error "sqn-display: bad index %s" index))
	  ((< index 1)
	   (error "index too small"))
	  ((> index (length sqns))
	   (error "index too large"))
	  (t t))
    (set-buffer sqn-buffer)
    (let ((sqn (sqn-find index)))
      (if sqn
	  (progn
	    (widen)
	    (narrow-to-region (sqn-start sqn)
			      (sqn-end sqn))
	    (if (not (null sqn-display-hook))
		(run-hooks 'sqn-display-hook)
	      (goto-char (point-max))
	      (re-search-backward assumption-assertion-separator-pattern))
	    (sqn-set-current-sqn index)
	    (setq mode-line-process
		  (format "Sqn %d%s of %d"
			  (sqn-index sqn)
			  (if (sqn-grounded-p sqn)
			      " (Grounded)"
			    "")
			  (length sqns))))))))
	

;;The following is vestigial. Tea calls it with the vstigial argument.

(defun sqn-select (one-based-index)
  (sqn-display one-based-index))

(defun sqn-display-jump (one-based-index)
  "Display the ONE-BASED-INDEXth (prefix arg) sqn in the sqn buffer."
  (interactive (list (prefix-numeric-value current-prefix-arg)))
  (sqn-display one-based-index))

(defun sqn-redisplay-last-seen ()
  "Display the sqn most recently viewed before this one (if any)."
  (interactive)
  (sqn-display (dgr-last-seen-sqn)))


(defun sqn-display-max () 
  "Display the maximum sqn in the sqn buffer."
  (interactive)
  (sqn-display (length (dgr-sqns))))
  
(defun sqn-redisplay ()
  "Display the current sqn in the sqn buffer."
  (interactive)
  (sqn-display (dgr-current-sqn)))
      
(defun sqn-display-next ()
  "Display the next sqn in the sqn buffer."
  (interactive)
  (sqn-display (1+ (dgr-current-sqn))))

(defun sqn-display-previous ()
  "Display the previous sqn in the sqn buffer."
  (interactive)
  (sqn-display (1- (dgr-current-sqn))))

(defun sqn-select-sqn-at-pos (here)
  "Display the sqn occupying the given position (point, interactively)
in the sqn buffer."
  (interactive (list (point)))
  (sqn-display (char-no->index here)))


(defun sqn-search-forward-regexp (search-string)
  (interactive "sRegexp search-string: ")
  (widen)
  (re-search-forward search-string nil nil)
  (sqn-select-sqn-at-pos (point)))


(defun sqn-add (index grounded text)
  (let ((sqn-buffer (dgr-sqn-buffer)))
    (save-excursion
      (set-buffer sqn-buffer)
      (let ((buffer-read-only nil))
	(widen)
	(let ((foundp (sqn-find index)))
	  (if foundp
	      (sqn-set-grounded-p foundp grounded)
	    (let ((new-sqn (make-sqn)))
	      (goto-char (point-max))
	      (sqn-set-start new-sqn (point-marker))
	      (insert text)
	      (sqn-set-end new-sqn
			   (set-marker (make-marker) (point-max)))
	      (sqn-set-index new-sqn index)
	      (sqn-set-grounded-p new-sqn grounded)
	      (dgr-sqns-adjoin new-sqn)
	      (sqn-set-current-sqn index))))))))

(defun sqn-add-from-file (sqn-file)
  "Add new sqns to sqns from printed representations in the sqn-file,
Assumes that the file contains a number of items of the form:
Index Grounded Text \^J\^L"
  (let ((tmp-buffer (get-buffer-create " dg-file.sqn")))
    (set-buffer tmp-buffer)
    (erase-buffer)
    (insert-file (expand-file-name (substitute-in-file-name sqn-file)))
    (let ((start (point-min))
	  end)
      (goto-char start)
      (while (re-search-forward page-delimiter nil t)
	(setq end (match-beginning 0))
	(let* ((str (buffer-substring start end))
	       (first-read (read-from-string str))
	       (second-read (read-from-string str (cdr first-read))))
	  (sqn-add (car first-read) 
		   (car second-read)
		   (substring str (cdr second-read))))
	
	(setq start (1+ end))
	(goto-char start)))
    (sqn-redisplay)))


(defun configure-window-and-attempt-sqn-display (index)
  (set-window-configuration *imps-window-configuration*)
  (condition-case
      v
      (sqn-display index)
    (error (sleep-for 1) (configure-window-and-attempt-sqn-display index))))

;;;(defun start-up-buffer-display 
;;;  (sqn-buffer-name dg-buffer-name dg-hash theory-string)
;;;	(dgrv-initialize-dgr
;;;	 (get-buffer-create sqn-buffer-name) 
;;;	 (get-buffer-create dg-buffer-name) 
;;;	 theory-string)
;;;	(set-buffer dg-buffer-name)
;;;	(dg-mode dgrv-index)
;;;	(set-buffer  sqn-buffer-name)
;;;	(sqn-mode dgrv-index)
;;;	(pop-to-buffer sqn-buffer-name)
;;;	(pop-to-buffer dg-buffer-name)
;;;	(setq *imps-window-configuration* (current-window-configuration)))

(defun number-list-to-string (nl)
  (mapconcat
   (function 
    (lambda (n)
      (format "%d" n)))
   nl
   ", "))

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    
