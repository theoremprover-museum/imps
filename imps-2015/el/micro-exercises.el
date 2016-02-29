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

(provide 'micro-exercises)

(defvar micro-exercise-list '())
(defvar current-micro-exercise-index -1)
(defvar micro-exercises-begun nil)

(defun add-micro-exercise (goal theory)
  (setq micro-exercise-list (append micro-exercise-list (list (cons goal theory)))))

(defun begin-micro-exercises ()
  (if micro-exercises-begun ""
    (progn
      (setq micro-exercises-begun t)
      (format "(load \"%s/micro-exercises.t\")" imps-exercise-directory))))

(defun imps-next-micro-exercise ()
  (interactive)
;  (begin-micro-exercises)
  (setq current-micro-exercise-index (1+ current-micro-exercise-index))
  (if (< current-micro-exercise-index (length micro-exercise-list))
      (start-current-micro-exercise)
    (error "You have now finished all the micro-exercises.")))

(defun imps-previous-micro-exercise ()
  (interactive)
  ;(begin-micro-exercises)
  (if (<= current-micro-exercise-index 0)
      (error "You are at the first micro-exercise.")
    (setq current-micro-exercise-index (1- current-micro-exercise-index))
    (start-current-micro-exercise)))

(defun imps-repeat-micro-exercise ()
  (interactive)
;  (begin-micro-exercises)
  (if (and (<= 0 current-micro-exercise-index)
	   (< current-micro-exercise-index (length micro-exercise-list)))
      (start-current-micro-exercise)
    (error "You have now finished all the micro-exercises.")))  

(defun start-current-micro-exercise ()

  ;; If the micro-exercises are already begun,  assume user really intends
  ;; to continue with new one)
  ;; OR
  ;; No *Sequent-nodes* buffer exists
  ;; OR
  ;; If *Sequent-nodes* buffer exists and user responds yes to query "Kill current proof?"
  ;; then start new one
  ;; otherwise ding
  (if (or micro-exercises-begun
	  (not  (get-buffer "*Sequent-nodes*"))
	  (yes-or-no-p "Kill current proof?"))
      
      (let* ((goal+theory (nth current-micro-exercise-index micro-exercise-list))
	     (load-p (begin-micro-exercises))
	     (goal (car goal+theory))
	     (theory (cdr goal+theory)))
	(tea-eval-large-expression
	 (format "(block
               %s
               (set (current-theory) (name->theory '%s))
               (clear-em) 
               (start-emacs-deduction \"%s\"))"
		 load-p
		 theory
		 goal)))
    (ding)))
  

(add-micro-exercise "forall(k,m:zz,
  1<=k and k<=m
   implies 
  (1+m)!/(k!*((1+m)-k)!)=comb(m,k-1)+comb(m,k))"
	      'h-o-real-arithmetic)

(add-micro-exercise "forall(k,m:zz,
  1<=k and k<=m implies comb(1+m,k)=comb(m,k-1)+comb(m,k))"
	      'h-o-real-arithmetic)

(add-micro-exercise "forall(k,m:zz,
  1<=k and k<=m implies comb(1+m,k)=comb(m,k-1)+comb(m,k))"
	      'h-o-real-arithmetic)

(add-micro-exercise "forall(k,m:zz,
  1<=k and k<=m implies comb(1+m,k)=comb(m,k-1)+comb(m,k))"
	      'h-o-real-arithmetic)

(add-micro-exercise
 "forall(m:zz, 0<=m implies sum(0,m,lambda(j:zz,j))=m*(m+1)/2)"
 'h-o-real-arithmetic)

(add-micro-exercise
 "forall(m:zz, 0<=m implies sum(0,m,lambda(j:zz,j))=m*(m+1)/2)"
 'h-o-real-arithmetic)

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    
