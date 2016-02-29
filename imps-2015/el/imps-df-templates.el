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


(provide 'imps-df-templates)

(defconst *def-form-template-alist* '())

(defun add-template (string)
  (setq *def-form-template-alist*
	(nconc
	 *def-form-template-alist*
	 (list
	  (cons
	   (substring string
		      1
		      (string-match " " string))
	   string)))))


;;;  (let ((start (string-match "def" string))
;;;	(end (string-match " " string)))
;;;    (if start
;;;	(setq *def-form-template-alist*
;;;	      (nconc
;;;	       *def-form-template-alist*
;;;	       (list
;;;		(cons
;;;		 (substring string
;;;			    start
;;;			    end)
;;;		 string))))
;;;      (setq *def-form-template-alist*
;;;	      (nconc
;;;	       *def-form-template-alist*
;;;	       (list
;;;		(cons
;;;		 (substring string
;;;			    1
;;;			    end)
;;;		 string))))))

(defun insert-template (def-form-name)
  "This command inserts a template for building a def-form specification into
the last visited scheme mode buffer (ignoring buffers which begin with
blanks) or, if none exists, creates a new scheme buffer. System will prompt 
user with a menu of def-form names."
  (interactive
   (list
    (completing-read-or-get-from-x-menu
     "Template: " *def-form-template-alist*  nil nil nil)))
  (let ((form (cdr (assoc def-form-name *def-form-template-alist*))))
    
    ;; This is included assuming that users will want to work in a 
    ;; scheme-mode buffer.
    
    (switch-to-buffer
     (or (mode-last-visited-buffer 'scheme-mode)
	 (prog1 (set-buffer (get-buffer-create "def-form-default.t"))
		(scheme-mode))))

    (push-mark (point) t)
    (if form (insert form))))

(add-template "(def-algebraic-processor PROCESSOR-NAME
  ;;optional cancellative ;;(assume cancellation for multiplication.)
  (language LANGUAGE-NAME)
  (base SPEC-FORMS)
  ;; optional (coefficient SPEC-FORMS)
  ;; optional (exponent SPEC-FORMS)
  ;; optional (syntax STRING-SYNTAX or SEXP-SYNTAX)
  )")

(add-template "(def-atomic-sort SORT-NAME
  QUASI-SORT-STRING
  (theory THEORY-NAME)
  (usages 
     ;; transportable-macete
     ;; rewrite
     ;; transportable-rewrite
     ;; d-r-value
     ;; d-r-convergence
  )
  ;; optional (witness WITNESS-EXPR-STRING)
  ;; optional (syntax STRING-SYNTAX or SEXP-SYNTAX)
  )")

(add-template "(def-cartesian-product PRODUCT-SORT-NAME
   (COMPONENT-SORT-1 ... )
   (theory THEORY-NAME)
   ;; optional (constructor CONSTRUCTOR)
   ;; optional (accessors ACCESSOR-1 ... )
   ;; optional (syntax STRING-SYNTAX or SEXP-SYNTAX)
   )")

(add-template "(def-compound-macete NAME
  SPEC)
  ;; SPEC is (repeat SPEC-1 ... )
  ;;        (parallel SPEC-1 ... ) stops at the first which succeeds
  ;;        (sequential SPEC-1 ... ) (stops when fails) 
  ;;        (series SPEC-1 ... )  (does them all)
  ;;        (without-minor-premises SPEC) does macete, 
  ;;         but without posting minor premises.
  ;;        (sound SPEC-1 CHECKER-1 CHECKER-2)
  )")

(add-template "(def-constant CONSTANT-NAME
  DEFINING-EXPR-STRING
  (theory THEORY-NAME)
  (usages 
     ;; transportable-macete
     ;; rewrite
     ;; transportable-rewrite
     ;; d-r-value
     ;; d-r-convergence
     ;; optional (syntax STRING-SYNTAX or SEXP-SYNTAX)
   ))")

(add-template
 "(def-imported-rewrite-rules THEORY	; An IMPS theory name
  ;; either of the following (or both) may be used:
  (source-theories THEORY-NAME_1 ...)
  ;; optional (source-theory THEORY-NAME_1)
  ;; optional (syntax STRING-SYNTAX or SEXP-SYNTAX)
  )")

(add-template "(def-inductor INDUCTOR-NAME
  INDUCTION-PRINCIPLE ;; String or name of induction principle.
  (theory THEORY-NAME)
  ;; optional (dont-unfold NAME-1 ... ); NAME can also be #t.
  ;; optional (translation NAME)
  ;; optional (base-case-hook MACETE-OR-COMMAND-NAME) 
  ;; optional (induction-step-hook MACETE-OR-COMMAND-NAME)
  ;; optional (syntax STRING-SYNTAX or SEXP-SYNTAX)
  )")

(add-template "(def-language LANGUAGE-NAME
  ;; optional (embedded-language NAME)
  ;; optional (embedded-languages NAME-1 ... )
  ;; optional (base-types TYPE-NAME-1 ... )
  ;; optional (sorts (SORT-NAME-1 ENCLOSING-SORT-NAME-1) ... )
  ;; optional (extensible (NUMERICAL-TYPE-1 SORT-NAME-1) ... )
  ;; optional (constants (CONSTANT-NAME-1 SORT-NAME-1) .... )
  ;; optional (syntax STRING-SYNTAX or SEXP-SYNTAX)
  )")

(add-template "(def-order-processor NAME
  (algebraic-processor PROCESSOR-NAME)
  (operations (OPERATION-TYPE OPERATOR)) ; OPERATION-TYPE is one of the symbols < <=.
  ;; optional (discrete-sorts SORT-1 ...)
  ;; optional (syntax STRING-SYNTAX or SEXP-SYNTAX)
  )")

(add-template "(def-overloading SYMBOL
  (LANGUAGE-NAME-1 SYMBOL-NAME-1) ...)")

(add-template "(def-parse-syntax CONSTANT ; An IMPS symbol name or list of them
  ;; optional (token SPEC) ;; a symbol or string.
  ;; optional (left-method PROC-NAME) ; e.g. infix-operator-method, postfix-operator-method
  ;; optional (null-method PROC-NAME) ; e.g. prefix-operator-method
  ;; optional (table TABLE-NAME) 
  (binding PRECEDENCE)
  ;; optional (syntax STRING-SYNTAX or SEXP-SYNTAX)
  )")

(add-template "(def-print-syntax CONSTANT ; An IMPS symbol name.
  ;; optional TEX
  ;; optional (token SPEC) ; a symbol or string.
  (method PROC-NAME) 
  ;; optional (table TABLE-NAME) 
  (binding PRECEDENCE)
  ;; optional (syntax STRING-SYNTAX or SEXP-SYNTAX)
  )")

(add-template "(def-quasi-constructor NAME
  LAMBDA-EXPR-STRING
  (language LANGUAGE-NAME)
  ;; optional (fixed-theories THEORY-NAME-1 ...)
  ;; optional (syntax STRING-SYNTAX or SEXP-SYNTAX)
  )")

(add-template "(def-record-theory THEORY-NAME
  (type NEW-TYPE-NAME)
  (accessors 
      (ACCESSOR-1 RANGE-SORT-1) ... )
  ;; optional (syntax STRING-SYNTAX or SEXP-SYNTAX)
  )")

(add-template "(def-recursive-constant NAMES ; A name or a list of names.
  DEFINING-FUNCTIONAL-STRINGS
  (theory THEORY-NAME)
  (usages 
     ;; transportable-macete
     ;; rewrite
     ;; transportable-rewrite
     ;; d-r-value
     ;; d-r-convergence
     ;; recursive-unfolding
  )
  ;; optional (definition-name DEF-NAME)
  ;; optional (syntax STRING-SYNTAX or SEXP-SYNTAX)
  )")

(add-template "(def-renamer RENAMER-NAME
  ;; optional (pairs 
  ;;            (OLD-NAME NEW-NAME) 
  ;;            ...)
  ;; optional (syntax STRING-SYNTAX or SEXP-SYNTAX)
  )")

(add-template "(def-schematic-macete MACETE-NAME
  FORMULA
  ;; optional null
  ;; optional transportable
  (theory LANGUAGE-NAME)
  ;; optional (syntax STRING-SYNTAX or SEXP-SYNTAX)
  )")


(add-template "(def-script THE-NAME
  INTEGER ;; Argument count for the script.
  (FORM-1 ... )
  ;; optional (retrieval-protocol PROTOCOL) ;; name of an emacs procedure
  ;; optional (syntax STRING-SYNTAX or SEXP-SYNTAX)
  )")

(add-template "(def-section SECTION-NAME
  ;; optional (component-sections COMP-SECTION-NAME-1 ...)
  ;; optional (files FILESPEC-1 ...)
  ;; optional (auxiliary-file FILESPEC)
  ;; optional (syntax STRING-SYNTAX or SEXP-SYNTAX)
  )")

;;;;;; The following code is for a double template:
;;;
;;;(defconst def-and-load-section-string "(def-section FILE-NAME
;;;  (files (imps theories/FILE-DIR/FILE-NAME)))
;;;
;;;(load-section FILE-NAME)")
;;;
;;;(setq *def-form-template-alist*
;;;	(nconc
;;;	 *def-form-template-alist*
;;;	 (list
;;;	  (cons
;;;	   "def-and-load-section"
;;;	   def-and-load-section-string))))

(add-template "(def-theorem THEOREM-NAME
  FORMULA-SPEC ;; A string or name of a theorem.
  (theory THEORY-NAME)
  (usages 
     ;; transportable-macete
     ;; rewrite
     ;; transportable-rewrite
     ;; d-r-value
     ;; d-r-convergence
  )
  ;; optional (translation TRANSLATION-NAME)
  ;; optional (macete MACETE-NAME)
  ;; optional (home-theory HOME-THEORY-NAME)
  ;; optional (proof PROOF-SCRIPT)
  ;; optional (syntax STRING-SYNTAX or SEXP-SYNTAX)
  )")


(add-template "(def-theory THEORY-NAME
  ;; optional (language LANGUAGE-NAME)
  ;; optional (component-theories THEORY-NAME-1 ... )
  (axioms
    
    (;; optional NAME
     FORMULA-STRING
     ;; transportable-macete
     ;; rewrite
     ;; transportable-rewrite
     ;; d-r-value
     ;; d-r-convergence
     ;; recursive-unfolding
    ) ... )
  ;; optional (distinct-constants (const-1 .... const-n) ... )
  ;; optional (syntax STRING-SYNTAX or SEXP-SYNTAX)
  )")

(add-template "(def-theory-ensemble THEORY-NAME
  ;; optional (fixed-theories THEORY-1 ... ) ;;default is (fixed-theories-set)
  ;; optional (replica-renamer PROCEDURE-NAME)
  ;; optional (syntax STRING-SYNTAX or SEXP-SYNTAX)
  )")


(add-template "(def-theory-ensemble-instances THEORY-ENSEMBLE-NAME

  ;; Exactly one of the following two keyword arguments must be present:

  ;; optional (target-theories THEORY-NAME-1 ... )
  ;; optional (target-multiple N) ;; same effect as (target-theory NAME-OF-REPLICA-1 ...)
  ;; optional (fixed-theories THEORY-1 ... ) ;;default is (fixed-theories-set)

  (sorts 
    (BASE-THEORY-SORT SORT-IN-TARGET-THEORY-1 ...)  
     ...)
  (constants
    (BASE-THEORY-CONSTANT CONSTANT-IN-TARGET-THEORY-1 ...)  
     ...)

  ;; Exactly one of the following two keyword arguments must be present:

  ;; optional (multiples MULTIPLE-1 ...)
  ;; optional (permutations P-1 .. )
  
  ;; optional (special-renamings RENAMING-1 ... )
  ;; optional (syntax STRING-SYNTAX or SEXP-SYNTAX)
  )")

(add-template "(def-theory-ensemble-multiple THEORY-ENSEMBLE-NAME
  N ;; an integer
  ;; optional (fixed-theories THEORY-1 ... ) 
  ;; optional (syntax STRING-SYNTAX or SEXP-SYNTAX)      
  )")

(add-template "(def-theory-ensemble-overloadings ENSEMBLE-NAME
  (MULTIPLE-1 ....)
  ;; optional (fixed-theories THEORY-1 ... ) 
  ;; optional (syntax STRING-SYNTAX or SEXP-SYNTAX)
  )")


(add-template "(def-theory-instance NAME
  (source SOURCE-THEORY-NAME)
  (target TARGET-THEORY-NAME)
  (translation TRANSLATION-NAME)
  ;; optional (fixed-theories THEORY-NAME-1 ... )
  ;; optional (renamer PROCEDURE-NAME)
  ;; optional (new-translation-name TRANSLATION-NAME)
  ;; optional (syntax STRING-SYNTAX or SEXP-SYNTAX)
  )")


(add-template "(def-translation NAME
  (source SOURCE-THEORY-NAME)
  (target TARGET-THEORY-NAME)
  ;; optional (assumptions FORMULA-STRING-1 ... )
  ;; optional (fixed-theories h-o-real-arithmetic ... )
  ;; optional (sort-pairs SORT-PAIR-SPEC-1 ... )
  ;; optional (constant-pairs CONSTANT-PAIR-SPEC-1 ... )
  ;; optional (core-translation CORE-TRANSLATION-NAME)
  ;; optional (syntax STRING-SYNTAX or SEXP-SYNTAX)
  (theory-interpretation-check using-simplification))")

(add-template "(def-transported-symbols NAMES ; A name or a list of names.
  (translation TRANSLATION-NAME)
  ;; optional (renamer PROCEDURE-NAME)
  ;; optional (syntax STRING-SYNTAX or SEXP-SYNTAX)
  )")
        	              				
(add-template "(include-files
  (files FILESPEC-1 ...)
  ;; optional RELOAD
  ;; optional QUICK-LOAD
  )")

(add-template "(load-section SECTION-NAME
  ;; optional RELOAD-FILES-ONLY
  ;; optional RELOAD
  ;; optional QUICK-LOAD
  )")

(add-template "(view-expr EXPRESSION-STRING
  ;; optional FULLY-PARENTHESIZE or FULLY
  ;; optional NO-QUASI-CONSTRUCTOR-FORMS or NO-QCS
  ;; optional TEX
  ;; optional (language LANGUAGE-NAME)
  ;; optional (syntax STRING or SEXP)
  ;; optional (syntax STRING-SYNTAX or SEXP-SYNTAX)
  )")







    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    
