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


;;; -*-Emacs-Lisp-*- Tea under emacs stuff.

;; This file is part of GNU Emacs.

;; GNU Emacs is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY.  No author or distributor
;; accepts responsibility to anyone for the consequences of using it
;; or for whether it serves any particular purpose or works at all,
;; unless he says so in writing.  Refer to the GNU Emacs General Public
;; License for full details.

;; Everyone is granted permission to copy, modify and redistribute
;; GNU Emacs, but only under the conditions described in the
;; GNU Emacs General Public License.   A copy of this license is
;; supposed to have been given to you along with GNU Emacs so you
;; can know your rights and responsibilities.  It should be in a
;; file named COPYING.  Among other things, the copyright notice
;; and this notice must be preserved on all copies.

;; xscheme.el adapted from shell.el to scheme.  
;; tea.el adapted for T from xscheme.el by J Rees.
;; Cream and sugar by Joshua Guttman and John D. Ramsdell.

;; Some suggestions for your .emacs file.
;; 
;;(autoload 'run-tea "tea"
;;	  "Run an inferior T process."
;;	  t)
;;
;; (setq auto-mode-alist
;;      (cons '("\\.t$" . scheme-mode)	; Scheme mode for T files.
;;	    auto-mode-alist))
;;

;; A suggestion for modifying the etags program so that it knows about T.
;; You should modify the few lines that allow etags to conclude that
;; files that end with ".t" are lisp source code.  Here is the differences
;; for the current version of etags.
;;364c364
;;<   /* .l or .el or .lisp (or .cl or .clisp or .t!) implies lisp source code */
;;---
;;>   /* .l or .el or .lisp (or .cl or .clisp or ...) implies lisp source code */
;;366d365
;;< 	     !strcmp (cp + 1, "t") ||

;; Modification by W. M. Farmer Mon Mar 22 2004
;; "send-string" replaced with "process-send-string".


(setq scheme-mit-dialect nil)
(provide 'tea)
;;;(require 'scheme)
;;;(require 'shell)

(defvar tea-use-comint nil
  "If non-nil, configure Tea mode for Shiver's comint process package.")
(defvar inferior-tea-mode-map nil)

(setq completion-ignored-extensions
      (append '(".mo" ".mi" ".mn" ".sd" ".so" ".si" ".sn")
	      completion-ignored-extensions))

(if inferior-tea-mode-map
    nil
  (setq inferior-tea-mode-map (copy-keymap shell-mode-map))
  (define-key inferior-tea-mode-map "\C-c\C-a"  'quit-shell-subjob)
  (define-key inferior-tea-mode-map "\C-c\C-g"  'interrupt-tea-process)
  (define-key inferior-tea-mode-map "\C-c\C-c"  'interrupt-tea-process)
  (define-key inferior-tea-mode-map "\C-d"	'delete-char-or-exit-breakpoint)
  (define-key inferior-tea-mode-map "\C-c\C-d"	'delete-char-or-exit-breakpoint)
;;  (define-key inferior-tea-mode-map "\C-x\C-e"	'tea-get-definition)
;;  (define-key inferior-tea-mode-map "\e\C-x"	'tea-get-definition)
;;  (define-key inferior-tea-mode-map "\e\C-l"	'tea-load-file)
  (define-key inferior-tea-mode-map "\e\C-c"	'tea-eval-expression)
  (define-key inferior-tea-mode-map "\C-c\C-y"	'yank-input)
  (define-key inferior-tea-mode-map "\ey"	'yank-pop-input-or-kill)
  (define-key inferior-tea-mode-map "\C-m"	'tea-send-input)
  (define-key inferior-tea-mode-map "\C-cl"	'tea-load-file)
  (define-key inferior-tea-mode-map "\C-cc"	'tea-compile-file)
  (define-key inferior-tea-mode-map "\C-co"	'tea-object-unhash)
  (define-key inferior-tea-mode-map "\t"	'scheme-indent-line)
  (define-key inferior-tea-mode-map "\177"	'backward-delete-char-untabify)
  (define-key inferior-tea-mode-map "\e\C-q"	'scheme-indent-sexp)
  (define-key inferior-tea-mode-map "\e "	'fixup-whitespace))

(if (not tea-use-comint)
    nil
  (define-key inferior-tea-mode-map "\ep" 'comint-previous-input)
  (define-key inferior-tea-mode-map "\en" 'comint-next-input)
  ;;   (define-key inferior-tea-mode-map "\en" 'comint-next-similar-input)
  ;;   (define-key inferior-tea-mode-map "\ep" 'comint-previous-similar-input)
  (define-key inferior-tea-mode-map "\es" 'comint-previous-similar-input)
  (define-key inferior-tea-mode-map "\C-m" 'comint-send-input)
  (define-key inferior-tea-mode-map "\C-d" 'comint-delchar-or-maybe-eof)
  (define-key inferior-tea-mode-map "\C-a" 'comint-bol)
  (define-key inferior-tea-mode-map "\C-c\C-u" 'comint-kill-input)
  (define-key inferior-tea-mode-map "\C-c\C-w" 'backward-kill-word)
  (define-key inferior-tea-mode-map "\C-c\C-c" 'comint-interrupt-subjob)
  (define-key inferior-tea-mode-map "\C-c\C-z" 'comint-stop-subjob)
  (define-key inferior-tea-mode-map "\C-c\C-\\" 'comint-quit-subjob)
  ;; Retained for compatibility with older shell mode, even though
  ;; ^D at end of buffer does the same thing.
  (define-key inferior-tea-mode-map "\C-c\C-d" 'comint-send-eof)
  (define-key inferior-tea-mode-map "\C-c\C-o" 'comint-kill-output)
  (define-key inferior-tea-mode-map "\C-cr"    'comint-previous-input-matching)
  (define-key inferior-tea-mode-map "\C-c\C-r" 'comint-show-output)
  ;;; Here's the prompt-search stuff I installed for RMS to try...
  (define-key inferior-tea-mode-map "\eP" 'comint-msearch-input)
  (define-key inferior-tea-mode-map "\eN" 'comint-psearch-input)
  (define-key inferior-tea-mode-map "\C-cR" 'comint-msearch-input-matching))


(define-key scheme-mode-map "\C-ce" 	'tea-send-definition)
(define-key scheme-mode-map "\C-c\C-e" 	'tea-send-definition-and-go)
;(define-key scheme-mode-map "\C-cc" 	'tea-compile-definition)
(define-key scheme-mode-map "\C-c\C-c" 	'tea-compile-definition-and-go)
(define-key scheme-mode-map "\C-c\C-g" 	'tea-reset-process)
(define-key scheme-mode-map "\C-cz" 	'switch-to-tea)
(define-key scheme-mode-map "\e\^Q" 	'scheme-indent-sexp)
(define-key scheme-mode-map "\eg" 	'balance-defuns)
(define-key scheme-mode-map "\eq" 	'fill-commented-paragraph)
(define-key scheme-mode-map "\e\C-i" 	'indent-relative)
(define-key scheme-mode-map "\e\C-m" 	'auto-fill-mode)
;; (define-key scheme-mode-map "\C-x\C-s" 	'balance-defuns-and-save)
(define-key scheme-mode-map "\e\C-c" 	'tea-eval-expression)
(define-key scheme-mode-map "\e "	'fixup-whitespace)


(defun inferior-tea-mode ()
  "Major mode for interacting with an inferior T process.

The following commands are available:
\\{inferior-tea-mode-map}

Entry to this mode calls the value of tea-mode-hook with no arguments,
if that value is non-nil.  Likewise with the value of shell-mode-hook.
tea-mode-hook is called after shell-mode-hook.

You can send text to the inferior Tea from other buffers
using the commands send-region, send-string and \\[tea-send-definition].

Commands:
Delete converts tabs to spaces as it moves back.
Tab indents for Scheme; with argument, shifts rest
 of expression rigidly with the current line.
Meta-Control-Q does Tab on each line starting within following expression.
Paragraphs are separated only by blank lines.  Semicolons start comments.

Return at end of buffer sends line as input.
Return not at end copies rest of line to end and sends it.
C-d at end of buffer sends end-of-file as input.
C-d not at end or with arg deletes or kills characters.
C-c C-c interrupts the shell or its current subjob if any.
C-z stops, likewise.  C-\\ sends quit signal, likewise.
There's other stuff too which isn't yet documented."

  (interactive)
  (kill-all-local-variables)
  (setq major-mode 'inferior-tea-mode)
  (setq mode-name "Tea under Emacs")
  (setq mode-line-process '(": %s"))
  (scheme-mode-variables)
  (use-local-map inferior-tea-mode-map)
  (make-local-variable 'last-input-start)
  (setq last-input-start (make-marker))
  (make-local-variable 'last-input-end)
  (setq last-input-end (make-marker))
  (if tea-use-comint
      (progn
	(make-local-variable 'comint-last-input-start)
	(setq comint-last-input-start (make-marker))
	(make-local-variable 'comint-last-input-end)
	(setq comint-last-input-end (make-marker))
	(make-local-variable 'comint-last-input-match)
	(setq comint-last-input-match "")
;; added by jt Wed Jun 15 14:58:37 EDT 1994

	(make-local-variable 'comint-last-output-start)
	(setq comint-last-output-start (make-marker))

	(make-local-variable 'comint-prompt-regexp)
	(setq comint-prompt-regexp "^>+ *")
	(make-local-variable 'input-ring-size) ; Don't set; default
	(make-local-variable 'input-ring) ; ...to global val.
	(setq input-ring nil)		; make sure it has a value here
	(make-local-variable 'input-ring-index)
	(setq input-ring-index 0)
	(make-local-variable 'comint-get-old-input)
	(make-local-variable 'comint-input-sentinel)
	(make-local-variable 'comint-input-filter)
	(setq comint-input-filter (function scheme-input-filter))
	(make-local-variable 'comint-input-sender)
	(make-local-variable 'comint-eol-on-send)
	(make-local-variable 'comint-ptyp)))    
  (run-hooks 'shell-mode-hook 'scheme-mode-hook 'inferior-tea-mode-hook))

(defvar inferior-scheme-filter-regexp "\\`\\s *\\S ?\\S ?\\s *\\'"
  "*Input matching this regexp are not saved on the history list.
Defaults to a regexp ignoring all inputs of 0, 1, or 2 letters.")

(defun scheme-input-filter (str)
  "Don't save anything matching inferior-scheme-filter-regexp"
  (not (string-match inferior-scheme-filter-regexp str)))


(defun args-to-list (string)
  (let ((where (string-match "[ \t]" string)))
    (cond ((null where) (list string))
	  ((not (= where 0))
	   (cons (substring string 0 where)
		 (args-to-list (substring string (+ 1 where)
					  (length string)))))
	  (t (let ((pos (string-match "[^ \t]" string)))
	       (if (null pos)
		   nil
		 (args-to-list (substring string pos (length string)))))))))

(defvar tea-program-name (expand-file-name "~jt/imps/executables/tea")
  "Program invoked by the tea and run-tea commands")

(defvar tea-process nil
  "Process currently running tea under emacs.")

(defvar show-tea-buffer (not (and (boundp 'major-version) (= major-version 19)))
  "If non-nil, pop to tea buffer when initially invoking tea.  
Default:  nil when in version 19.")

(defun tea-maybe-pop-to-buffer (buffer)
  (and
   show-tea-buffer
   (pop-to-buffer buffer)))


(defun run-tea ()
  "Run an inferior the process which is the value of tea-program-name
Input and output via buffer *tea*."
  (interactive)
  (save-excursion
    (message "Loading IMPS ...")
    (set-buffer
     (make-shell "tea" tea-program-name nil))
    (inferior-tea-mode)
    (setq tea-process (get-buffer-process "*tea*"))
    (process-send-string tea-process "(in-package \"TEA\")\n")	 
    (message "Loading IMPS ... done.")))

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
       (push-mark)
       (goto-char next-end)
       (cond ((interactive-p)
	      (ding)	      
	      (message "Unbalanced defun."))
	     (t nil))))))

(defun balance-defuns-and-save (force)
  "Call balanced-defuns on current-buffer and save it if all defuns are balanced. 
Prefix arg means force save without checking for balance."
  (interactive "P")
  (if (or force (balance-defuns (current-buffer)))
      (save-buffer)
    (ding)
    (message "Unbalanced defun -- buffer not saved.")))

(defun switch-to-tea ()
  "Switch to the *tea* buffer."
  (interactive)
  (pop-to-buffer "*tea*"))

(defvar tea-script-buffer
  (let ((buff (get-buffer-create " *Tea script*"))
	(fn   (if (eq t (car (file-attributes (expand-file-name "~/imps/"))))
		  (expand-file-name "~/imps/ *Tea script*")
		(expand-file-name "~/ *Tea script*"))))
    (set-buffer buff)
    (set-visited-file-name fn)
    (scheme-mode)
    (set-buffer-modified-p nil)
    buff)
  "Buffer used to accumulate script of current Tea session")

(defvar tea-process-busy-p nil
  "Flag Tea process is currently computing.")
     
(defun tea-eval-expression (str)
  "Read a string from the minibuffer and send it to inferior tea process."
  (interactive "sTea Eval: ")
  (save-excursion
    (set-buffer tea-script-buffer)
    (goto-char (point-max))
    (insert str)
    (insert "\n"))

; This is new. 

  (save-excursion
    (set-buffer "*tea*")
    (set-marker comint-last-output-start (point-max)))
  (process-send-string tea-process (concat str "\n"))

; used to be as follows:
; I don't understand why repl-wont-print is included. This seems
; to add a new and unnecessary (and confusing) prompt.

;  (process-send-string tea-process (concat str " repl-wont-print\n"))

)


(defun tea-send-definition ()
  "Send the current definition to the Tea process made by M-x run-tea."
  (interactive)
  (save-excursion
    (end-of-defun)
    (let ((end (point)))
      (beginning-of-defun)
      (tea-eval-large-expression
       (buffer-substring (point) end))
      (process-send-string tea-process "\n"))))

(defun tea-funcall (fn-str arg-str)

  "Read a FN-STR and ARG-STR from the minibuffer and send (funcall
  FN-STR ARG-STR) to inferior tea process."

  (interactive "sTea Function: \nsArguments: ")
  (tea-eval-expression
   (format "(funcall %s %s)" fn-str arg-str)))

(defun tea-send-definition-and-go ()
  "Send the current definition to the inferior Tea, and switch to *tea* buffer."
  (interactive)
  (tea-send-definition)
  (switch-to-tea))

;;;(defun tea-compile-definition ()
;;;  "Compile the current definition to the T process made by M-x run-tea."
;;;  (interactive)
;;;  (save-excursion
;;;   (end-of-defun)
;;;   (let ((end (point)))
;;;     (beginning-of-defun)
;;;     (process-send-string tea-process "(compile '")
;;;     (send-region tea-process (point) end)
;;;     (process-send-string tea-process ")\n"))))
;;;
;;;(defun tea-compile-definition-and-go ()
;;;  "Send and compile the current definition to the inferior T, and switch to *tea* buffer."
;;;  (interactive)
;;;  (tea-compile-definition)
;;;  (switch-to-tea))

(defvar tea-exit-breakpoint-char ?\^D)

(defun delete-char-or-exit-breakpoint (arg)
  "Delete ARG characters forward, or if at end of buffer, exit repl,
the current read-eval-print loop in T."
  (interactive "p")
  (if (eobp)
      (process-send-string tea-process (format "%c\n" tea-exit-breakpoint-char))
      (delete-char arg)))

(defun interrupt-tea-process ()
  "Send an interrupt to  tea-process."
  (interactive)
  (interrupt-process tea-process))


(defun continue-tea-process ()
  "continue tea-process."
  (interactive)
  (process-send-string tea-process "(ret)\n repl-wont-print\n"))

(defvar input-ring '()
  "List of put-in text sequences.")

(defvar input-ring-yank-pointer '()
  "The tail of the input ring whose car is the last thing yanked.")

;;; Newline

(defun tea-send-input ()
  "Send input to inferior T process."
  (interactive nil)
  (if tea-use-comint
      (comint-send-input)
    (shell-send-input)
    (save-excursion
      (goto-char last-input-end)
      (if (bolp) (backward-char))
      (copy-region-as-input last-input-start (point)))))

(defun copy-region-as-input (beg end)
  "Save the region as if put in, but don't put it in."
  (interactive "r")
  (setq input-ring (cons (buffer-substring beg end) input-ring))
  (if (> (length input-ring) kill-ring-max)
      (setcdr (nthcdr (1- kill-ring-max) input-ring) nil))
  (setq input-ring-yank-pointer input-ring))

(defun rotate-input-pointer (arg)
  "Rotate the yanking point in input ring."
  (interactive "p")
  (let ((length (length input-ring)))
    (if (zerop length)
	(error "Input ring is empty")
      (setq input-ring-yank-pointer
	    (nthcdr (% (+ arg (- length (length input-ring-yank-pointer)))
		       length)
		    input-ring)))))

;;; Meta-Y

(defun yank-pop-input-or-kill (arg)
  "Replace just-yanked stretch of killed-text with a different stretch.
This command is allowed only immediately after a  yank , yank-input ,
or itself.
At such a time, the region contains a stretch of reinserted
previously-killed text.  yank-pop  deletes that text and inserts in its
place a different stretch of killed text.

With no argument, the previous kill is inserted.
With argument n, the n'th previous kill is inserted.
If n is negative, this is a more recent kill.

The sequence of kills wraps around, so that after the oldest one
comes the newest one."
  (interactive "*p")
  (if (eq last-command 'yank)
      (yank-pop arg)
    (if (not (eq last-command 'yank-input))
	(error ;"Previous command was not a yank"
	 (symbol-name last-command))
      (progn
	(setq this-command 'yank-input)
	(let ((before (< (point) (mark))))
	  (delete-region (point) (mark))
	  (rotate-input-pointer arg)
	  (set-mark (point))
	  (insert (car input-ring-yank-pointer))
	  (if before (exchange-point-and-mark)))))))

;;; Control-Meta-Y

(defun yank-input (&optional arg)
  "Reinsert the last input.
With just C-U as argument, same but put point in front (and mark at end).
With argument n, reinsert the nth most recent input.
See also the command \\[yank-pop-input-or-kill]."
  (interactive "*P")
  (rotate-input-pointer (if (listp arg) 0
			  (if (eq arg '-) -1
			    (1- arg))))
  (push-mark (point))
  (insert (car input-ring-yank-pointer))
  (if (consp arg)
      (exchange-point-and-mark)))

(defun tea-object-unhash()
  "Insert (object-unhash ) and poise cursor before left-paren."
  (interactive)
  (insert-string "(object-unhash )")
  (backward-char 1))

(defun tea-load-file (file-name)
  "Load a Tea file into the inferior Tea process."
  (interactive
   (list
    (expand-file-name
     (read-file-name "Load Tea file: " default-directory "" t))))
  (tea-eval-expression (concat "(load \""
			       file-name
			       "\"\)\n"))
  (switch-to-tea))

(defun tea-compile-file (file-name)
  "Compile a Tea file in the inferior Tea process."
  (interactive "fCompile Tea file: ")		
  (process-send-string tea-process (concat "(compile-file \""
			     file-name
			     "\"\)\n"))
  (switch-to-tea))


(defun tea-chdir (dir)
  "Switch tea process to new current-directory."
  (interactive "DChange to directory: ")
  (process-send-string tea-process (concat "(tea::chdir \""
			     (substring (expand-file-name dir) 0 -1)
			     "\"\)\n"))
  (switch-to-tea)
  (setq default-directory dir))

(put 'labels 'scheme-indent-hook 1)
(put 'xcase 'scheme-indent-hook 1)
(put 'select 'scheme-indent-hook 1)
(put 'xselect 'scheme-indent-hook 1)
(put 'typecase 'scheme-indent-hook 1)
(put 'destructure 'scheme-indent-hook 1)
(put 'destructure* 'scheme-indent-hook 1)
(put 'with-open-ports 'scheme-indent-hook 1)
(put 'with-input-from-string 'scheme-indent-hook 1)
(put 'bind 'scheme-indent-hook 1)
(put 'bind* 'scheme-indent-hook 1)
(put 'iterate 'scheme-indent-hook 2)
(put 'receive 'scheme-indent-hook 1)
(put 'block 'scheme-indent-hook 0)
(put 'catch 'scheme-indent-hook 1)
(put 'object 'scheme-indent-hook 1)
(put 'operation 'scheme-indent-hook 1)
(put 'join 'scheme-indent-hook 0)

(if (and (boundp 'major-version)
	 (= major-version 19))
    (progn 
      (put 'labels 'scheme-indent-function 1)
      (put 'xcase 'scheme-indent-function 1)
      (put 'select 'scheme-indent-function 1)
      (put 'xselect 'scheme-indent-function 1)
      (put 'typecase 'scheme-indent-function 1)
      (put 'destructure 'scheme-indent-function 1)
      (put 'destructure* 'scheme-indent-function 1)
      (put 'with-open-ports 'scheme-indent-function 1)
      (put 'with-input-from-string 'scheme-indent-function 1)
      (put 'bind 'scheme-indent-function 1)
      (put 'bind* 'scheme-indent-function 1)
      (put 'iterate 'scheme-indent-function 2)
      (put 'receive 'scheme-indent-function 1)
      (put 'block 'scheme-indent-function 0)
      (put 'catch 'scheme-indent-function 1)
      (put 'object 'scheme-indent-function 1)
      (put 'operation 'scheme-indent-function 1)
      (put 'join 'scheme-indent-function 0)))


(modify-syntax-entry ?[ "(]" scheme-mode-syntax-table)
(modify-syntax-entry ?] ")[" scheme-mode-syntax-table)
(modify-syntax-entry ?{ "(}" scheme-mode-syntax-table)
(modify-syntax-entry ?} "){" scheme-mode-syntax-table)



(defvar communication-file (concat  "/tmp/" (getenv "USER") "-tea-eval.t"))

(defun tea-eval-large-expression (str)
  "Cause a string to be written to file and loaded by the inferior tea process."
  (save-excursion
    (set-buffer tea-script-buffer)
    (goto-char (point-max))
    (insert str)
    (insert "\n"))
  (write-region str nil communication-file)
  (tea-eval-expression (format "(load \"%s\")" communication-file)))


(defun tea-eval-large-expression-and-update-sqn-and-dg (str)
  (tea-eval-large-expression
   (format "(execute-call-from-emacs-and-update %s)" str))
  (message "Calling Tea..."))



    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    
