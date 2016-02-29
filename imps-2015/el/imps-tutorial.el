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



(provide 'imps-tutorial)


(defconst imps-exercise-already-sent-marker (make-marker)
  "Marker object to point to endpoint of material already evaluated by T 
in the current IMPS exercise.")
(defconst imps-exercise-tmp-file
  (format "/tmp/exercise-imps-%s.t" (user-login-name))
  "Temporaray file for portion of IMPS exercise to be loaded by T.")
(defconst imps-exercise-pattern "(!)"
  "Pattern indicating next exercise for IMPS.")
(defconst imps-def-theorem-pattern "^(def-theorem")

(defun imps-exercise-next-target ()
  "Search for the next exercise, and send text between
imps-exercise-already-sent-marker  and next exercise to T."
  (interactive)
  (if (or (not
	   (bufferp (marker-buffer imps-exercise-already-sent-marker)))
	  (not
	   (integerp (marker-position imps-exercise-already-sent-marker))))
      (goto-char (point-min))
    (set-buffer (marker-buffer imps-exercise-already-sent-marker))
    (goto-char (marker-position imps-exercise-already-sent-marker)))
  (let ((start (point)))
    (if (not (search-forward imps-exercise-pattern nil t))
	(progn
	  (set-marker imps-exercise-already-sent-marker nil)
	  (message "Current exercise completed."))
      (write-region start (point) imps-exercise-tmp-file nil 0)
      (process-send-string
       tea-process
       (format "(load \"%s\")\n" imps-exercise-tmp-file))
      (set-marker imps-exercise-already-sent-marker (point))
      (message "Sent previous text from buffer to Tea process."))))
	
(defun imps-exercise-start-in-current-file ()
  "Start in on the exercise in the current buffer."  
  (interactive)
  (goto-char (point-min))
  (set-marker imps-exercise-already-sent-marker (point))
  (imps-exercise-next-target))

(defun exercise-source-file ()
  (let* ((name 
	  (file-name-nondirectory (buffer-file-name)))
	 (source (substitute-in-file-name 
		  (format (concat imps-exercise-directory "/%s") name)
		  ;; Formerly: (format "$THEORIES/exercises/%s" name)
		  )))
    (if (file-exists-p source)
	source
      (error "This is not an exercise-file!"))))
    
;;First find name of theorem:

(defun working-on ()
  (save-excursion
    (let ((next-p (re-search-forward "def-theorem" (point-max) t)))
      (if next-p
	  (progn 
	    (save-excursion
	      (let ((beg (progn (beginning-of-defun) (point)))
		    (end (progn (forward-sexp) (point))))
		(goto-char beg)
		(if (re-search-forward "proof" end t)
		    (error "Next def-theorem form already has a proof!"))))
	    
	    (re-search-forward "[ \t\n]*")
	    (let ((beg (point)))
	      (re-search-forward "[ \t\n]")
	      (backward-char 1)
	      (buffer-substring beg (point))))
	(error "There is no def-theorem form following point!")))))

;;Extract the proof from answer:

(defun locate-proof (theorem-name)
  (save-excursion
    (find-file-read-only (exercise-source-file))
    (goto-char (point-min))
    (re-search-forward theorem-name)
    (re-search-forward "proof")
    (re-search-backward "(")
    (let ((beg (point)))
      (forward-sexp)
      (prog1 (buffer-substring beg (point))
	(bury-buffer)))))

(defun locate-and-insert-proof ()
  (interactive)
  (let ((script (locate-proof (working-on))))
    (save-excursion
      (let ((next-p (re-search-forward imps-def-theorem-pattern (point-max) t)))
	(if next-p
	    (progn
	      (re-search-backward "(")
	      (forward-sexp)
	      (backward-char 1)
	      (insert script))
	  (error "There is no def-theorem form following point!"))))))
  

(defun delete-all-exercise-proofs ()
  (save-excursion
    (goto-char (point-min))
    (while (re-search-forward  imps-def-theorem-pattern (point-max) t)
      (locate-and-delete-next-proof))))    


(defun locate-and-delete-next-proof ()
  (let ((bound (save-excursion (re-search-backward "(")
			       (forward-sexp)
			       (point))))
    (let ((has-proof-p (re-search-forward "proof" bound t)))
      (if has-proof-p 
	  (progn
	    (re-search-backward "(")
	    (let ((beg (point)))
	      (forward-sexp)
	      (delete-region beg (point))))))))


    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    
