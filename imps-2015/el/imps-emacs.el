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

(defmacro if-error-notify-but-dont-break (expr)
  (list 'condition-case
	'v
	expr
	'(error (message (mapconcat (function (lambda (x) (format "%s" x)) ) (cdr v) " ")))))

(if (v19-fsf-p)
    (progn

      (setq initial-frame-alist '((left . 20)
				  (border-color . "yellow")
				  (foreground-color . "white")
				  (menu-bar-lines . 1)
				  (cursor-color . "yellow")
				  (top . 70) 
				  (left . 70)
				  (font . "-Misc-Fixed-Medium-R-Normal--20-200-75-75-C-100-ISO8859-1")
				  (background-color . "midnight blue")
				  (top . 10)
				  (width . 80)
				  (height . 30)
				  (name . "IMPS")))

      (setq transient-mark-mode t)
      (put 'eval-expression 'disabled nil)

      (if-error-notify-but-dont-break
       (set-face-background 'region "light blue"))
      (if-error-notify-but-dont-break
       (set-face-foreground 'region "black"))
      (if-error-notify-but-dont-break
       (set-face-foreground 'italic "turquoise"))
      (if-error-notify-but-dont-break
       (set-face-foreground 'bold-italic "green"))
      (if-error-notify-but-dont-break
       (set-face-background 'bold-italic nil))

      (if-error-notify-but-dont-break
       (set-face-background 'modeline "#775588"))
      (if-error-notify-but-dont-break
       (set-mouse-color "green"))
      (setq-default mode-line-buffer-identification '("Buffer: %20b"))

      (modify-frame-parameters (selected-frame) '((top . 80) (left . 70) (width . 95) (height . 35)))

      ;;
      (setq *max-menu-size* 25)

      (if-error-notify-but-dont-break
       (set-face-background 'highlight "red"))
      (if-error-notify-but-dont-break
       (set-face-foreground 'highlight "white"))

					;DISABLE OVERWRITE MODE!

      (define-key global-map [insert] nil)
      (fmakunbound 'overwrite-mode)

      (define-key global-map [menu-bar file df-find] '("IMPS find file" . df-find-file))

      (menu-bar-mode 1))
  

  (progn
    (setq initial-frame-plist '(left  20
				      border-color  "yellow"
				      foreground-color  "white"
				      menu-bar-lines  1
				      cursor-color  "yellow"
				      top  15
				      left  10
				      font  "misc-fixed-*-*-normal-*-14-*-*-*-*-94-*-*"
				      background-color  "steel blue"
				      width  95
				      height  30
				      name  "IMPS"))

    (set-frame-properties (selected-frame) '(height  30 width  95 left  10 top  15))
    (set-face-background 'default "light gray")
    (set-face-foreground 'default "midnight blue")

    (add-hook 'scheme-mode-hook 'font-lock-mode)
    (add-hook 'dg-mode-hook 'font-lock-mode)
    (if-error-notify-but-dont-break
     (set-face-foreground 'font-lock-def-form-name-face "white"))
    (if-error-notify-but-dont-break
     (set-face-foreground 'font-lock-def-form-face "blue"))
    (if-error-notify-but-dont-break
     (set-face-background 'font-lock-def-form-name-face "steel blue"))
    (if-error-notify-but-dont-break
     (set-face-background 'zmacs-region "light blue"))
    (if-error-notify-but-dont-break
     (set-face-foreground 'italic "turquoise"))
    (if-error-notify-but-dont-break
     (set-face-foreground 'bold-italic "green"))
    (if-error-notify-but-dont-break
     (set-face-foreground 'font-lock-comment-face "steel blue"))
    (if-error-notify-but-dont-break
     (set-face-background 'modeline "dark gray"))
    (if-error-notify-but-dont-break
     (set-face-foreground 'modeline "black"))
    (if-error-notify-but-dont-break
     (set-face-background 'modeline-buffer-id "dark gray"))
    (if-error-notify-but-dont-break
     (set-face-foreground 'modeline-buffer-id "blue"))
    (if-error-notify-but-dont-break
     (set-face-background 'modeline-mousable  "dark gray"))
    (if-error-notify-but-dont-break
     (set-face-foreground 'modeline-mousable "black"))

    (setq-default mode-line-buffer-identification '("Buffer: %20b"))
    (setq pop-up-windows nil)
    (add-hook 'df-listing-mode-hook 'imps-set-buffer-toolbar)
    (add-hook 'scheme-mode-hook 'imps-set-buffer-toolbar)
    (add-hook 'sqn-mode-hook 'imps-set-buffer-toolbar)
    (add-hook 'w3-mode-hook 'imps-set-buffer-toolbar)
    (add-hook 'w3-mode-hook #'(lambda () (setq truncate-lines nil)))))
;;w3 stuff:

(if (v19-lucid-p)
    (progn 
      (if-error-notify-but-dont-break
       (require 'w3))

      (if-error-notify-but-dont-break
       (require 'w3-toolbar))

      (defun imps-home ()
	(interactive)
	(switch-to-buffer (get-buffer-create "IMPS")))

      (defun imps-tea ()
	(interactive)
	(switch-to-buffer (get-buffer-create "*tea*")))

      (defun imps-sqn ()
	(interactive)
	(let ((buff (get-buffer "*Sequent-nodes*")))
	  (if buff (switch-to-buffer  buff)
	    (message "No *Sequent-nodes* buffer currently active"))))

      (if (featurep 'w3)
	  (progn 
	    (add-hook 'imps-hooks
		      (lambda() 
			(w3-open-local  (in-vicinity imps-source-files "../http/startup-imps.html"))
			(imps-reset-menubar)))
      
	    (if-error-notify-but-dont-break
	     (progn
	       (nconc (assoc "application" mm-mime-data) '(("scheme" ("viewer" . scheme-mode) ("type" . "application/scheme"))))

	       (nconc mm-mime-extensions '((".t"       . "application/scheme")))
	       ))
	    (put 'w3-mode 'mode-toolbar-icons
		 '((xpm startdg imps-start-deduction "Start a new deduction")
		   (xpm section imps-load-section "Loads a section")
		   (xpm theory set-current-theory "Sets the current theory")
		   () 
		   (xpm exercise imps-next-micro-exercise "Start Micro Exercise (or Next micro exercise)")
		   (xpm home-up imps-home "Return to IMPS home window")
		   (xpm tea imps-tea "Go to *tea* buffer")
		   (xpm sqn imps-sqn "Go to *Sequent-node* buffer")))))

      (put 'sqn-mode 'mode-toolbar-icons 
	   '((xpm bang imps-x-command-menu "apply a command") 
	     (xpm breakup dg-direct-and-antecedent-inference-strategy "Break up the formula")
	     (xpm macete apply-macete-with-minor-premises-menu "Apply a macete")
	     (xpm simplify dg-simplify "Simplify current node")
	     ()
	     (xpm exercise imps-next-micro-exercise "Start Micro Exercise (or Next micro exercise)")
	     (xpm home-up  imps-home "Return to IMPS home window")
	     (xpm tea imps-tea "Go to *tea* buffer")
	     (xpm sqn imps-sqn "Go to *Sequent-node* buffer")
	     (xpm tex sqn-xview "View formatted current sequent node")
	     (xpm prev sqn-display-previous "Display previous sequent")
	     (xpm next sqn-display-next "Display next sequent")
	     (xpm parent imps-parent "Visit parent node")
	     (xpm child imps-first-child "Visit first child node")))

      (put 'scheme-mode 'mode-toolbar-icons 
	   '((xpm startdg imps-start-deduction "Start a new deduction")
	     (xpm section imps-load-section "Loads a section")
	     (xpm theory set-current-theory "Sets the current theory")
	     ()
	     (xpm home-up  imps-home "Return to IMPS home window")  
	     (xpm tea imps-tea "Go to *tea* buffer")
	     (xpm sqn imps-sqn "Go to *Sequent-node* buffer")
	      
	     ))

      (put 'scheme-mode 'initial-toolbar-spec 't)

      (put 'inferior-tea-mode 'initial-toolbar-spec 't)
      (put 'inferior-tea-mode 'mode-toolbar-icons 
	   '((xpm startdg imps-start-deduction "Start a new deduction") 
	     (xpm section imps-load-section "Loads a section")
	     (xpm theory set-current-theory "Sets the current theory")
	     () 
	     (xpm home-up  imps-home "Return to IMPS home window")
	     (xpm tea imps-tea "Go to *tea* buffer")
	     (xpm sqn imps-sqn "Go to *Sequent-node* buffer"))) 

      (put 'df-listing-mode 'mode-toolbar-icons 
	   '((xpm startdg imps-start-deduction "Start a new deduction")
	     (xpm section imps-load-section "Loads a section")
	     (xpm theory set-current-theory "Sets the current theory")
	     ()
	     (xpm home-up  imps-home "Return to IMPS home window")
	     (xpm tea imps-tea "Go to *tea* buffer")
	     (xpm prev df-show-previous-def-form "Display previous def-form")
	     (xpm next df-show-next-def-form "Display next def-form")

	     ))

      (put 'df-listing-mode 'initial-toolbar-spec 't)

      (defun shrink-window (N &optional SIDE WINDOW) nil)

      (defun enlarge-window (N &optional SIDE WINDOW) nil)))


    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    
