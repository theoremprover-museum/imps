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


;; support process filtering for T process.

(provide 'process-filter)
;;;(require 'sexps)
;;;(require 'tea)

(defun toggle-process-filter (arg)
  "Toggle whether process-output from ARG is simply inserted in its buffer, or
is given a chance to be evaluated by emacs.  ARG may be a process, a buffer, a
buffer-name, or a buffer name sans *'s."
  (interactive
   (list
    (or (get-buffer-process (current-buffer))
	(read-from-minibuffer "Process in buffer: "))))
  (let ((proc
	 (cond ((processp arg) arg)
	       ((bufferp arg) (get-buffer-process arg))
	       ((and (stringp arg)
		     (get-buffer-process arg)))
	       ((stringp arg)
		(get-buffer-process
		 (concat "*" arg "*"))))))
    (cond ((process-filter proc)
	   (set-process-filter proc nil)
	   (process-send-string proc "(unset-emacs-process-filter)\n")
	   (message "Process filter for %s off now." proc))
	  (t
	   (set-process-filter proc 'process-output-insert-or-eval)
	   (process-send-string proc "(set-emacs-process-filter)\n")
	   (message "Process filter for %s on now." proc)))))

(defun turn-on-process-filter (arg &optional expr)
  "Ensure process-output from ARG is given a chance to be evaluated by emacs.  
ARG may be a process, a buffer, a buffer-name, or a buffer name sans *'s."
  (interactive
   (list
    (or (get-buffer-process (current-buffer))
	(read-from-minibuffer "Process in buffer: "))))
  (let ((proc
	 (cond ((processp arg) arg)
	       ((bufferp arg) (get-buffer-process arg))
	       ((and (stringp arg)
		     (get-buffer-process arg)))
	       ((stringp arg)
		(get-buffer-process
		 (concat "*" arg "*"))))))
    (set-process-filter proc 'process-output-insert-or-eval)
    (process-send-string proc (format "(block (set-emacs-process-filter) %s)\n" expr))
    (message "Process filter for %s on now." proc)))

(defconst tea-prompt-pattern "\^J>+ *\\'")

(defun buffer-visible-p (buff)
  "t iff BUFF is currently visible in some window."
  (if (get-buffer-window buff) t nil))

(defun insert-process-output (proc output)
  "OUTPUT goes to PROC's process-buffer." 
  (set-buffer
    (process-buffer proc))
  (goto-char (point-max))
  (insert output)
  (set-marker (process-mark proc) (point)))

(defun noisy-insert-process-output (proc output)
  "OUTPUT goes to PROC's process-buffer, and echo area if buffer not visible." 
  (set-buffer
    (process-buffer proc))
  (goto-char (point-max))
  (insert output)
  (set-marker (process-mark proc) (point))
  (or (buffer-visible-p			;echo to echo area if buffer
	(process-buffer proc))		;not displayed, after
      (if (string-match		        ;discarding newline & prompt
	    tea-prompt-pattern
	    output)
	  (message
	    (substring
	      output 0
	      (match-beginning 0)))
	(message output))))

(defvar emacs-eval-remnant nil
  "Left over piece of text from process output waiting for emacs-eval-end.")

(make-variable-buffer-local 'emacs-eval-remnant)

(defconst emacs-eval-start ?\035)
(defconst emacs-eval-end ?\036)
(defconst emacs-uneval-start ?\037)

(defun process-output-insert-or-eval (proc output)
  "Insert normal OUTPUT in PROC's process buffer, and execute emacs forms."
  (let ((oldbuff (current-buffer)))
    (set-buffer (process-buffer proc))
    (if emacs-eval-remnant
	(setq output (concat emacs-eval-remnant output)
	      emacs-eval-remnant nil))
    (let* ((start-index 0)
	   (eval-start
	    (string-char-pos-after output emacs-eval-start start-index))
	   (eval-end
	    (and eval-start
		 (string-char-pos-after output emacs-eval-end eval-start))))
      (while (and eval-start
		  eval-end)
	(if (> eval-start start-index)
	    (insert-process-output proc (substring output start-index eval-start)))
	(eval-output-string output (1+ eval-start) eval-end)
	(setq start-index (1+ eval-end)
	      eval-start (string-char-pos-after output emacs-eval-start start-index)
	      eval-end (and eval-start
			    (string-char-pos-after output emacs-eval-end eval-start))))
      (insert-process-output
       proc
       (substring output start-index eval-start))
      (if eval-start
	  (setq emacs-eval-remnant
		(substring output eval-start))))
    (set-buffer oldbuff)))

(defun eval-output-string (str start end)
  (condition-case error-data
      (let ((uneval
	     (string-char-pos str emacs-uneval-start)))
	(if uneval
	    (funcall
	     (car (read-from-string str start uneval))
	     (substring str (1+ uneval) end))
	  (eval
	   (car
	    (read-from-string str start end)))))
    (error (ding)
	   (with-output-to-temp-buffer "*IMPS Notification Buffer*"
	     (princ (format "Process Filter error: %s" error-data))))))


;; (defun eval-output-string (str start end)
;;   (eval
;;    (car
;;     (read-from-string str start end))))

;; (defun process-read-line (proc str)
;;   (if (string-match "\n" str)
;;       (process-send-string proc str)
;;     (process-send-string proc (concat str "\n"))))
;; 
(defun get-new-tea-buffer (name)
  "Get a `new' tea stream buffer named NAME 
 by killing the old one or making it not read-only."
  (let ((buff (get-buffer-create name)))
    (set-buffer buff)
    (setq buffer-read-only nil)
    buff))
 
(defun tea-buff-mode ()
  (setq major-mode 'tea-buff-mode)
  (setq mode-name "Tea Buff")
  (make-local-variable 'last-input-end)
  (setq last-input-end (make-marker))
  (set-marker last-input-end (point-min)))
;;   
;; (defun read-line-from-tea-buff (buff)
;;   (set-buffer buff)
;;   (save-excursion 
;;     (let* ((start (save-excursion
;; 		    (goto-char (marker-position last-input-end))
;; 		    (beginning-of-line 2)
;; 		    (point)))
;; 	   (end   (save-excursion
;; 		    (goto-char start)
;; 		    (end-of-line 1)
;; 		    (point))))	    
;;       (if (>= start (point-max))
;; 	  (process-send-string proc "*eof*\n")
;; 	(process-send-string
;; 	 tea-process
;; 	 (concat (buffer-substring start end) "\n"))))))
;; 
;; (defun reset-tea-buff-marker (buff)
;;   "Move the input marker back to the front of BUFF, a tea stream buffer." 
;;   (interactive "bTea stream buffer: ")
;;   (set-buffer buff)
;;   (set-marker last-input-end (point-min)))
;; 
;; (defun clear-tea-buff (buff)
;;   "Erase contents of BUFF, a tea stream buffer." 
;;   (interactive "bTea stream buffer: ")
;;   (set-buffer buff)
;;   (erase-buffer))

;; (defmacro setq-to-tea-value (symbol tea-form)
;;   "Setq SYMBOL to the result of evaluating tea-form in the T process."
;;   (set-to-tea-value symbol tea-form))
;; 
;; (defun set-to-tea-value (symbol tea-form)
;;   "Set SYMBOL to the result of evaluating tea-form in the T process."
;;   (process-send-string
;;    tea-process
;;    (format "(emacs-eval \"(setq %s ~A)\" %s)\n" symbol tea-form)))

(defun tea-reset-process (really)
  "Send subordinate tea-process an interrupt and then a reset."
  (interactive
   (list
    (y-or-n-p "Reset tea process [confirm]: ")))
  (message "")
  (if (or (not really) tea-gc-now)
      (message "Tea process not reset.")
    (interrupt-process tea-process t)
    (process-send-string tea-process "(reset)\n")
    (message "Tea process reset.")))

;; (defun tea-shell (command-string)
;;   "Prompt for command name and execute it in *tea-shell*,
;; initialized to execute in $IMPS_TMP if the latter is defined."
;;   (interactive
;;    (list (read-from-minibuffer "Command: " nil shell-completion-map)))
;;   (or (get-buffer "*tea-shell*")
;;       (let ((buff (get-buffer-create "*tea-shell*")))
;; 	(set-buffer buff)
;; 	(setq default-directory (if (fboundp 'imps-tmp-dir)
;; 				    (imps-tmp-dir)
;; 				  "/tmp/"))))
;;   (or (get-buffer-process "*tea-shell*")
;;       (progn
;; 	(message "Starting tea-shell process")
;; 	(process-kill-without-query
;; 	 (get-buffer-process
;; 	  (make-shell "tea-shell" "csh")))))
;;   (set-buffer "*tea-shell*")
;;   (erase-buffer)
;;   (send-string "tea-shell" (concat command-string "\n")))

(defvar tea-literal-file
  (expand-file-name
   (substitute-in-file-name
    (format "/tmp/%s-literals.txt" (user-login-name)))))

(defvar tea-return-number 0)

(defun read-from-tea-literal-file ()
  (save-excursion
    (let ((buff (get-buffer-create " *Tea Literal*")))
      (set-buffer buff)
      (erase-buffer)
      (insert-file-contents tea-literal-file)
      (goto-char (point-min))
      (condition-case var
	  (read buff)
	(invalid-read-syntax
	 (message "Invalid read syntax: %s" (car (cdr var)))
	 nil)))))

(defun get-literal-from-tea (str)
  (let ((next-return (1+ tea-return-number)))
    (condition-case var
	(progn
	  (process-send-string
	   tea-process
	   (format 
	    "(with-open-ports ((lf (open \"%s\" '(out))))
	     (print %s lf)
	     (emacs-eval \"(setq tea-return-number %d)\"))\n"
	    tea-literal-file
	    str
	    next-return))
	  (while (not (= tea-return-number next-return))
	    (sleep-for 1))
	  (read-from-tea-literal-file))
      (quit (progn
	      (setq tea-return-number next-return)
	      (if (not tea-gc-now)
		  (tea-reset-process t)
		(imps-error
		 (format "%s  %s"
			 "Emacs cannot interrupt Tea now."
			 "\nPlease let it terminate before next call to get-literal-from-tea."))))))))
      



    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    
