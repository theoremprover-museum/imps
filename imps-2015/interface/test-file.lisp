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


;; Procedures for analysing test file results.  

;;; 313. THEOREM-NAME: DIST-CONTINUITY-LEMMA
;;; 
;;; forall(x,y,z:pp,abs(dist(x,z)-dist(y,z))<=dist(x,y));
;;; 
;;; THEORY: METRIC-SPACES
;;; SEQUENT NODES: 12
;;; PROOF STEPS: 5
;;; GROUNDED?: YES
;;; CONTEXTS=9
;;; ASSUMPTIONS/CONTEXT=1.7777777777777777
;;; Q-POPULATION/CONTEXT=33.77777777777778
;;; Q-POPULATION-MAXIMUM=59
;;; predecessor-max=3
;;; subset-count-max=3
;;; Max-Index=7
;;; virtual time = 11.75 seconds


(defun compact-imps-test-file (obarray-name record-buffer)
  "Produce an obarray summary of the IMPS test file in the current buffer"
  (interactive "SVariable name to hold obarray: \nP")
  (if record-buffer
      (setq record-buffer
	    (get-buffer-create
	     (read-buffer "Buffer for output: "))))
  (and (= major-version 18)
       (error "Please execute in version 19"))
  (goto-char (point-min))
  (let ((the-obarray (make-obarray)))
    (condition-case signal-stuff
	(while (compact-read-next-record the-obarray record-buffer))
      (error (message "%s" (cdr signal-stuff))))
    (set obarray-name the-obarray)
    the-obarray))

(defun compact-read-next-record (the-obarray record-buffer)
  "Get info from next IMPS test theorem record, advancing point."
  (let ((case-fold-search nil))
    (and
     (search-forward "THEOREM-NAME:" nil 1)
     (let* ((start (match-beginning 0))
	    (thm-name (next-symbol-string (point))))
       (if (not (intern-soft thm-name the-obarray))
	   (compact-read-next-record-1 (intern thm-name the-obarray) record-buffer)
	 (compact-read-next-record-1
	  (intern
	   (format
	    "theorem-number-%s"
	    (save-excursion
	      (goto-char start)
	      (beginning-of-line nil)
	      (read (current-buffer))))
	    the-obarray)
	  record-buffer))))))

(defun compact-read-next-record-1 (sym record-buffer)
  "Glean the IMPS test data for SYM, moving point forward and returning non-nil."
  (let* ((original-buffer (current-buffer))
	 (start (point))
	 (end
	  (save-excursion
	    (if (not (search-forward "virtual time" nil t))
		(error "Incomplete record")
	      (end-of-line nil)
	      (point)))))
    (and (bufferp record-buffer)
	 (progn
	   (set-buffer record-buffer)
	   (insert (format "\n%s\n " sym))
	   (set-buffer original-buffer)))
    (put sym 'char-pos start)
    (if (search-forward "GROUNDED?:" end t)
	(let ((val (string= (next-symbol-string (point)) "YES")))
	  (put sym 'grounded val)
	  (and (bufferp record-buffer)
	       (progn
		 (set-buffer record-buffer)
		 (insert (format "%s " val))
		 (set-buffer original-buffer))))
      (put sym 'grounded 'incomplete))
    (mapcar 
     (function
      (lambda (search-str+prop-name)
	(let ((search-str (car search-str+prop-name))
	      (prop-name (cdr search-str+prop-name)))
	  (goto-char start)
	  (if (search-forward search-str end t)
	      (let ((val (read (current-buffer))))
		(put sym prop-name
		     (if (floatp val)
			 (floor val)
		       val)))
	    (put sym prop-name '()))
	  (and (bufferp record-buffer)
	       (progn
		 (set-buffer record-buffer)
		 (insert (format "%s " (get sym prop-name)))
		 (set-buffer original-buffer)))
	  t)))
		
     '(("SEQUENT NODES:" . nodes) ("PROOF STEPS:" .  steps)
       ("CONTEXTS=" .  contexts) ("ASSUMPTIONS/CONTEXT=" .  avg-assums)
       ("Q-POPULATION/CONTEXT=" .  avg-q-pop)
       ("Q-POPULATION-MAXIMUM=" . max-q-pop) ("predecessor-max=" .  max-preds)
       ("subset-count-max=" . max-subsets)  ("Max-Index=" .  max-index)
       ("virtual time =" .  virtual-time)))))
       
(defun imps-records-agree-p (sym1 sym2)
  (every-p
   (mapcar
    (function
     (lambda (prop-name)
       (let ((val1 (get sym1 prop-name))
	     (val2 (get sym2 prop-name)))
	 (if (and (numberp val1) (numberp val2))
	     (= val1 val2)
	   (eq val1 val2)))))
    '(nodes steps grounded contexts avg-assums avg-q-pop
	    max-q-pop max-preds max-preds max-subsets max-index))))

(defun imps-records-improve-time (sym1 sym2)
  "Virtual time for the first theorem improves that for the second."
  (let ((time1 (get sym1 'virtual-time))
	(time2 (get sym1 'virtual-time)))
    (and time1 time2
	 (< (get sym1 'virtual-time)
	    (get sym2 'virtual-time)))))

(defun imps-records-unproved-theorems (the-obarray)
  (let ((unproved-theorems '()))
    (mapatoms
     (function
      (lambda (sym)
	(or (get sym 'grounded)
	    (setq unproved-theorems
		  (cons sym unproved-theorems)))))
     the-obarray)
    unproved-theorems))

(defvar slower-theorems '())
(defvar not-in-old '())


(defun imps-records-show-deterioration (new-obarray old-obarray)
  (setq slower-theorems '())
  (setq not-in-old '())
  (mapatoms
   (function
    (lambda (new-sym)
      (let ((old-sym (intern-soft (symbol-name new-sym) old-obarray)))
	(if old-sym
	    (or (imps-records-improve-time new-sym old-sym)
		(setq slower-theorems
		      (cons new-sym slower-theorems)))
	  (setq not-in-old (cons new-sym not-in-old))))))
   new-obarray)
  slower-theorems)

(defun imps-records-print-times (new-obarray old-obarray)
  (mapatoms
   (function
    (lambda (new-sym)
      (let ((new-time (get new-sym 'virtual-time)))
	(insert (format
		 "Thm: %s\n   Time: %s Old Time: %s\n\n"
		 new-sym (get new-sym 'virtual-time)
		 (get (intern-soft (symbol-name new-sym) old-obarray) 'virtual-time))))))
   new-obarray))

(defun imps-records-avg-time (new-obarray)
  (interactive "XObarray name: ")
  (let ((count 0)
	(sum 0))
    (mapatoms
     (function
      (lambda (new-sym)
	(let ((new-time (get new-sym 'virtual-time)))
	  (setq count (1+ count))
	  (setq sum (+ sum new-time)))))
     new-obarray)
    (if (interactive-p)
	(message "Number of theorems: %s; Total time: %s; Average time: %s"
		 count sum (/ (float sum) count))
      (insert (format "\nNumber of theorems: %s; Total time: %s\n"
		      count sum))
      (insert (format "Average time: %s\n"
		      (/ (float sum) count))))))
	    

(defun imps-records-print-times-sum (new-obarray old-obarray)
  (let ((new-sum 0)
	(old-sum 0))
    (mapatoms
     (function
      (lambda (new-sym)
	(let ((new-time (get new-sym 'virtual-time))
	      (old-time (get
			 (intern-soft (symbol-name new-sym) old-obarray)
			 'virtual-time)))
	  (if (and new-time old-time)
	      (progn
		(setq new-sum (+ new-sum new-time))
		(setq old-sum (+ old-sum old-time)))))))
     new-obarray)
    (format "New Time: %s Old Time: %s" new-sum old-sum)))

(defun imps-records-print-compact (the-obarray)
  (mapatoms
   (function
    (lambda (new-sym)
      (mapcar
       (function
	(lambda (prop-name)
	  (insert (format "%s " (get new-sym prop-name)))))
       '(nodes steps grounded contexts avg-assums avg-q-pop
	       max-q-pop max-preds max-preds max-subsets max-index))
      (insert "\n")))
   the-obarray))

(defun imps-records-show-differences (new-obarray old-obarray)
  (let ((differences '()))
    (mapatoms
     (function
      (lambda (new-sym)
	(let ((old-sym (intern-soft (symbol-name new-sym) old-obarray)))
	  (if old-sym
	      (or (imps-records-agree-p new-sym old-sym)
		  (setq differences
			(cons new-sym differences)))))))
     new-obarray)
    differences))

(defun every-p (lst)
  (let ((ok t))
    (while (and ok lst)
      (if (car lst)
	  (setq lst (cdr lst))
	(setq ok nil)))
    ok))

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    
