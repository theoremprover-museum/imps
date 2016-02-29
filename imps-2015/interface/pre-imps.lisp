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

;;; Start IMPS with "M-x run-imps".

(defvar imps-alter-load-path t "Non-nil (default) means loading IMPS will alter load path.")
(defvar imps-edit-window-configuration nil "Stores window configuration for use in IMPS-edit")
(defconst major-version (read (substring emacs-version  0 2))
  "Number of major version of this incarnation of emacs, either 18 or 19")


(defun v18p ()
  "True if using FSF v18.whatever."
  (= major-version 18))

(defun v19p ()
  "True if using FSF v19."
  (<= 19 major-version ))


(defun v19-lucid-p ()
  "True if using Lucid lemacs v19."
  (and (<= 19  major-version)
       (string-match "Lucid" emacs-version)))

(defun v19-fsf-p ()
  "True if using FSF emacs v19."
  (and (= major-version 19)
       (not (string-match "Lucid" emacs-version))))


(defun in-vicinity (dir pathname)
  (substitute-in-file-name (expand-file-name (concat dir pathname))))

(defvar imps-theory-files "/home/jt/imps/")
(defvar imps-preferred-directory
  (let ((dir (expand-file-name "~/imps/theories/")))
    (if (file-exists-p dir)
	dir
      (in-vicinity imps-theory-files "")))
  "Directory in which to run IMPS, normally ~/imps/theories/ if that exists; otherwise 
$IMPS/theories/.")
  
(defvar imps-source-files (substitute-in-file-name "/home/jt/imps/oolong/"))

(setq auto-mode-alist
      '(("\\.t$" . imps-theory-mode) 
	("\\.el$" .emacs-lisp-mode) 
	("\\.l$" . lisp-mode) ("\\.lisp$" . lisp-mode)
	("\\.TeX$" . TeX-mode)
	("\\.bib$" .bibtex-mode) ("\\.article$" . text-mode)
	("\\.imps$" . scheme-mode)
	("\\.ool$" . scheme-mode)
	("\\.lsp$" . lisp-mode) ("/\\..*emacs" . emacs-lisp-mode)))	


(defvar input-ready-prompt ">")

(defvar imps-program-name (in-vicinity imps-source-files "../bin/climps"))

(defconst imps-files
  (cond 

   ((and window-system (v19-lucid-p))
    '(tea sexps process-filter theory-information sqns imps-edit protocols 
		     deduction-graphs imps-commands imps-manual
		     imps-df-templates imps-proof-edit imps-lucid-support
		     imps-tutorial micro-exercises def-form-edit imps ))

   ((and window-system (v19p))
    '(tea sexps process-filter theory-information sqns imps-edit protocols 
		     deduction-graphs imps-commands imps-manual
		     imps-df-templates imps-proof-edit imps-fsf-support
		     imps-tutorial micro-exercises def-form-edit imps ))

   (window-system
    '(tea sexps process-filter theory-information sqns imps-edit protocols
		     deduction-graphs imps-commands imps-manual
		     imps-df-templates imps-proof-edit imps-x-support
		     imps-tutorial micro-exercises def-form-edit imps))
   (t '(tea sexps process-filter theory-information sqns imps-edit protocols
		       deduction-graphs imps-commands imps-manual
		       imps-df-templates imps-proof-edit
		       imps-tutorial micro-exercises def-form-edit imps))))


(if (and (boundp imps-alter-load-path)
	 imps-alter-load-path)
    (setq load-path 
	  (cons (in-vicinity imps-source-files "../el")
		load-path)))

(defvar imps-finish-load-message "Loading init files ... done.")
(defvar init-files-loaded nil "True if IMPS init files loaded. Should be t after startup")

(setq imps-alter-load-path nil)

(setq tea-exit-breakpoint-char ?\^E)

(defun run-imps ()
  (interactive)
  (require 'scheme)
  (require 'backquote)
  (require 'shell)
  (require 'font-lock)
  (mapcar #'(lambda (sym) (require sym)) imps-files)
  (or (fboundp 'make-shell)
      (fset 'make-shell 'make-comint))
  (let ((tea-program-name imps-program-name))
    (run-tea)
    (set-process-filter tea-process 'process-output-insert-or-eval)
    (switch-to-buffer "*tea*")
    (imps-xview-start-xdvi)
;;For cmu and allegro, put these in.
;;;(imps-load-init-files)
))


(defun imps-load-init-files ()
  (interactive)
  (message "Loading init files ...")
  (if (v19-fsf-p)
      (sit-for 1 0 t)
    (sit-for 1 t))
  (process-send-string tea-process "(block (load '(oolong-compiled user/init))\n)"))
				     
;;;"(block (load '(oolong-compiled user/init)) (format t \"IMPS Version 2.0~%Authors: W. M. Farmer, J. D. Guttman, F. J. Thayer~%~%Current Theory: ~A\" (name (current-theory))) (force-output (standard-output)))\n"))

;;;(defun imps-load-init-files ()
;;;  (interactive)
;;;  (message "Loading init files ...")
;;;  (if (v19-fsf-p)
;;;      (sit-for 1 0 t)
;;;    (sit-for 1 t))
;;;  (tea-eval-large-expression
;;;   "#+(lisp::or clisp kcl cmu) (load '(oolong-compiled user/init)) #+allegro (block (load '(oolong-compiled user/init)) (t-impl::init-reader t-impl::*readtable*))
;;;      (block (format t \"IMPS Version 2.0~%Authors: W. M. Farmer, J. D. Guttman, F. J. Thayer~%~%Current Theory: ~A\" (name (current-theory))) (force-output (standard-output)) (emacs-eval \"(progn (setq init-files-loaded t)(message imps-finish-load-message))\"))"))
;;;


(defun quit-imps ()
  (interactive)
  (if (y-or-n-p "Confirm: Quit IMPS? ")
      (let ((name-of-process "*tea*"))
	(process-send-string name-of-process "(exit)\n")
	(set-buffer tea-script-buffer)
	(save-buffer))
    (ding)
    (recenter)))



(defconst major-version (read (substring emacs-version  0 2))
  "Number of major version of this incarnation of emacs, either 18 or 19")

(setq tea-use-comint (<= 19 major-version ))


    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    
