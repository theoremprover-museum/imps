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


(provide 'imps-manual)

(defvar xse-program-name
  (in-vicinity imps-source-files "../src/xse/xse"))

(defvar imps-manual-index
  (in-vicinity imps-source-files "../doc/manual/manual.idx"))

(defvar view-manual-process '())

(defun imps-view-manual ()
  "Start up xdvi on manual."
  (interactive)
  (let ((default-directory
	  (in-vicinity imps-source-files "../doc/manual/")))
    (setq view-manual-process
	  (start-process "imps-manual" nil "xdvi" "-iconic" "-keep"
			 "-s" "3" "manual"))))

(defun imps-goto-manual-page (num)
  (start-process "xse" nil xse-program-name "manual.dvi" (format "%dg" (1+ num))))

(defvar imps-manual-alist '())

(defun imps-manual-entry-get-arg ()
  (or imps-manual-alist
      (let ((buff
	     (or (get-buffer " *IMPS manual index*")
		 (progn (set-buffer (get-buffer-create " *IMPS manual index*"))
			(insert-file-contents imps-manual-index)
			(get-buffer " *IMPS manual index*")))))
	(set-buffer buff)
	(goto-char (point-min))
	(while (search-forward "\\indexentry{" nil 0 nil)
	  (setq 
	   imps-manual-alist
	   (cons
	    (list
	     (next-symbol-string (point)))
	    imps-manual-alist)))))
  (imps-completing-read 
   "Index entry: " imps-manual-alist))
    
(defun imps-manual-entry (str)
  (interactive (list (imps-manual-entry-get-arg)))    
  (or (get-buffer " *IMPS manual index*")
      (progn (set-buffer (get-buffer-create " *IMPS manual index*"))
	     (insert-file-contents imps-manual-index)))
  (if (and (processp view-manual-process)
	   (eq 'run (process-status view-manual-process)))
      (let ((buffer (get-buffer " *IMPS manual index*")))
	(set-buffer buffer)
	(goto-char (point-min))
	(if (not (search-forward (concat "\\indexentry{" str) nil t))
	    (error "Index entry %s not found." str)
	  (up-list 1)
	  (down-list 1)
	  (let ((num (car (read-from-string (next-symbol-string (point))))))
	    (imps-goto-manual-page num)
	    (message "Displaying page %d" num))))
    (imps-view-manual)
    (message "Starting xdvi on IMPS manual.  Please re-execute when icon appears.")))
      
	
(defun imps-manual-tutorial ()
  (interactive)
  (if (and (processp view-manual-process)
	   (eq 'run (process-status view-manual-process)))
      (imps-goto-manual-page 7)
    (imps-view-manual)
    (message "Starting xdvi on IMPS manual.  Please re-execute when icon appears.")))
    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    
