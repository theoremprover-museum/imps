;; Copyright (c) 1990-1994 The MITRE Corporation
;; 
;; Authors: W. M. Farmer, J. D. Guttman, F. J. Thayer
;;   
;; The MITRE Corporation (MITRE) provides this software to you without
;; charge to use, copy, modify or enhance for any legitimate purpose
;; provided you reproduce MITRE's copyright notice in any copy or
;; derivative work of this software.
;; 
;; This software is the copyright work of MITRE.  No ownership or other
;; proprietary interest in this software is granted you other than what
;; is granted in this license.
;; 
;; Any modification or enhancement of this software must identify the
;; part of this software that was modified, by whom and when, and must
;; inherit this license including its warranty disclaimers.
;; 
;; MITRE IS PROVIDING THE PRODUCT "AS IS" AND MAKES NO WARRANTY, EXPRESS
;; OR IMPLIED, AS TO THE ACCURACY, CAPABILITY, EFFICIENCY OR FUNCTIONING
;; OF THIS SOFTWARE AND DOCUMENTATION.  IN NO EVENT WILL MITRE BE LIABLE
;; FOR ANY GENERAL, CONSEQUENTIAL, INDIRECT, INCIDENTAL, EXEMPLARY OR
;; SPECIAL DAMAGES, EVEN IF MITRE HAS BEEN ADVISED OF THE POSSIBILITY OF
;; SUCH DAMAGES.
;; 
;; You, at your expense, hereby indemnify and hold harmless MITRE, its
;; Board of Trustees, officers, agents and employees, from any and all
;; liability or damages to third parties, including attorneys' fees,
;; court costs, and other related costs and expenses, arising out of your
;; use of this software irrespective of the cause of said liability.
;; 
;; The export from the United States or the subsequent reexport of this
;; software is subject to compliance with United States export control
;; and munitions control restrictions.  You agree that in the event you
;; seek to export this software or any derivative work thereof, you
;; assume full responsibility for obtaining all necessary export licenses
;; and approvals and for assuring compliance with applicable reexport
;; restrictions.
;; 
;; 
;; COPYRIGHT NOTICE INSERTED: Mon Apr 11 11:42:27 EDT 1994


(provide 'cmpn)

(defvar cmpn-mode-map (copy-keymap scheme-mode-map) "Keymap for cmpn-mode.")

(defun cmpn-mode ()
  "Major mode for carrying out computations in IMPS.
Commands:
\\{cmpn-mode-map}\n"
  (interactive)
  (kill-all-local-variables)
  (use-local-map cmpn-mode-map)
  (setq major-mode 'cmpn-mode)
  (setq mode-name "IMPS Computation")
  (scheme-mode-variables)
  (setq mode-line-buffer-identification
	(list "  %1*>> %b <<%1*  "))
  (setq mode-line-format
	(list (dgrv-fn-at 'dgr-theory-name dg-number)
	      ": " 'mode-line-process "       " 'mode-line-buffer-identification "       "
	      'global-mode-string
	       "  %3p %1*%1*"))
  (run-hooks 'cmpn-mode-hook))

(defvar sqn-nos-referenced
  '()
  "List of sequent node numbers referred to by a computation node.")
(make-variable-buffer-local 'sqn-nos-referenced)

(defvar cmpn-index nil)
(make-variable-buffer-local 'cmpn-index)

(defun add-cmpn (dgrv-index index sqn-nos text)
  (let ((cmpn-vector (dgrv-fn-at 'dgr-cmpn-vector dgrv-index)))
    (if (< index (length cmpn-vector))
	(let ((buff (get-buffer-create
		     (format "*Computations-%d-%d*" dgrv-index index))))
	  (aset cmpn-vector index buff)
	  (set-buffer buff)
	  (or (eq major-mode 'cmpn-mode)
	      (cmpn-mode))
	  (setq dg-number dgrv-index
		cmpn-index index)
	  (setq sqn-nos-referenced
		(let ((l nil))
		  (while sqn-nos
		    (or (memq (car sqn-nos) sqn-nos-referenced)
			(setq l (cons (car sqn-nos) l)))
		    (setq sqn-nos (cdr sqn-nos)))
		  (append sqn-nos-referenced (nreverse l))))
	  (setq mode-line-process
		(format "From sqn%s %s"
			(if (< 1 (length sqn-nos-referenced))
			    "s"
			  "")
			(number-list-to-string sqn-nos-referenced)))
	  (erase-buffer)
	  (insert text)
	  (goto-char (point-min))
	  buff)
      (dgrv-fn-at
       (function
	(lambda (dgr)
	  (dgr-set-cmpn-vector dgr (vconcat cmpn-vector (make-vector 10 nil)))))
       dgrv-index)
      (add-cmpn dgrv-index index sqn-nos text))))

(defun cmpn-add-from-file (dgrv-index cmpn-file)
  "Add exactly one new cmpn to cmpn-vector from printed representations in the cmpn-file,
Assumes that the file contains just one item of the form:
Index Sqn-nos Text
where Index is an integer, Sqn-nos is a list of integers, and Text is arbitrary text."
  (let ((tmp-buffer (get-buffer-create " dg-file.cmpn")))
    (set-buffer tmp-buffer)
    (erase-buffer)
    (insert-file (expand-file-name (substitute-in-file-name cmpn-file)))
    (let* ((str (buffer-string))
	   (index-read (read-from-string str))
	   (sqns-read (read-from-string str (cdr index-read))))
      (setq tmp (list index-read sqns-read))
      (add-cmpn dgrv-index (car index-read) (car sqns-read)
		(substring str (cdr sqns-read))))))

(defun cmpn-add-and-display (dgrv-index cmpn-file)
  (let ((buff
	 (cmpn-add-from-file dgrv-index cmpn-file)))
    (pop-to-buffer buff)))

(defun cmpn-post-expression ()
  (interactive)
  (let ((text-and-end (imps-expression-at-point)))
    (tea-eval-expression
     (format "(computation-node-read %d %d \"%s\")"
	     dg-number
	     cmpn-index
	     (car text-and-end)))))

(defun sexp-last (l)
  (while (not (null (cdr l)))
    (setq l (cdr l)))
  (car l))

(defun cmpn-display-sqn ()
  (interactive)
  (sqn-display dg-number (1- (sexp-last sqn-nos-referenced)))
  (switch-to-buffer-other-window (sqn-buffer)))

(defun cmpn-simplify-expression ()
  (interactive)
  (let ((text-and-end (imps-expression-at-point)))
    (tea-eval-expression
     (format "(computation-node-simplify %d %d \"%s\")"
	     dg-number
	     cmpn-index
	     (car text-and-end)))))

(defun cmpn-apply-macete ()
  (interactive)
  (let ((text-and-end (imps-expression-at-point)))
    (tea-eval-expression
     (format "(computation-node-apply-macete %d %d \"%s\" %s)"
	     dg-number
	     cmpn-index
	     (car text-and-end)
	     (funcall 'macete-retrieval-protocol)))))
    

(define-key cmpn-mode-map "\C-c." 'cmpn-display-sqn)
(define-key cmpn-mode-map "\C-c\C-c" 'cmpn-post-expression)
(define-key cmpn-mode-map "\C-c\C-s" 'cmpn-simplify-expression)
(define-key cmpn-mode-map "\C-c\C-m" 'cmpn-apply-macete)

    

    

    

    

    
