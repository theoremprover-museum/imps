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
; Emulation of TEA in Common Lisp for IMPS: Author F. J. Thayer.
; 
; 
; COPYRIGHT NOTICE INSERTED: Wed Mar  5 13:36:30 EST 1997

;;Assumes variable imps is set. Called from shell


(setq *imps-files*
      '("user/def-forms" 
	"user/other-forms"
	"resources/numerical-objects"
	"resources/bitop-numerical-objects"
	"resources/emacs-buffers"
	"resources/lisp-supplements"
	"resources/sets"
	"expressions/sortings"
	"expressions/expressions"
	"expressions/constructors"
	"expressions/quasi-constructors"
	"expressions/innards-for-constructors"
	"expressions/innards-for-languages"
	"expressions/languages"
	"substitution/substitutions"
	"substitution/substitution-application"
	"substitution/alpha-equivalence"
	"substitution/naive-matching"
	"substitution/sort-substitutions"
	"substitution/variable-sorts-matching"
	"expressions/some-constructors"
	"expressions/some-quasi-constructors"
	"expressions/gently"
	"expressions/quasi-sorts"
	"expressions/schemata-for-quasi-constructors"
	"expressions/virtual-paths"
	"presentation/read-print"
	"theory-mechanism/domain-range"
	"theory-mechanism/definitions"
	"theory-mechanism/recursive-definitions"
	"theory-mechanism/sort-definitions"
	"theory-mechanism/mc-extensions"
	"theory-mechanism/sort-constructors"
	"theory-mechanism/history"
	"theory-mechanism/theorem"
	"theory-mechanism/restricted-substitution-definedness"
	"theory-mechanism/transforms"
	"theory-mechanism/theory-transform-interface"
	"theory-mechanism/rewrite-rules"
	"theory-mechanism/transportable-rewrite-rules"
	"theory-mechanism/elementary-macetes"
	"theory-mechanism/transportable-macetes"
	"theory-mechanism/theory-subsorting"
	"theory-mechanism/theory"
	"theory-mechanism/theory-ensembles"
	"theory-mechanism/record-theories"
	"theory-mechanism/sections"
	"inferences/q-classes"
	"inferences/context-sequent"
	"inferences/context-entailment"
	"inferences/syllogistic-inference"
	"inferences/backchain"
	"inferences/rules"
	"inferences/deduction-graphs"
	"inferences/constructor-inferences"
	"inferences/special-rules"
	"inferences/domain-range-inference"
	"inferences/domain-range-rules"
	"inferences/commands"
	"inferences/dg-primitive-inferences"
	"inferences/dg-inferences-interface"
	"inferences/relative-position"
	"inferences/scripts"
	"inferences/informal-justification"
	"presentation/dg-emacs"
	"presentation/theory-emacs"
	"presentation/read-interface"
	"presentation/parse"
	"presentation/presentation-interface"
	"presentation/print"
	"presentation/tex-print-methods"
	"presentation/xtv-interface"
	"presentation/tex-prescriptive-presentation"
	"presentation/sexp-print"
	"presentation/sexp-syntax"
	"presentation/overloading"
	"presentation/macete-help"
	"theory-inference/algebraic"
	"theory-inference/expand"
	"theory-inference/reductions"
	"theory-inference/order"
	"theory-inference/feasible"
	"theory-inference/context-inequalities"
	"theory-inference/equality"
	"theory-inference/macetes"
	"theory-inference/macete-constructors"
	"theory-mechanism/the-kernel-theory"
	"theory-inference/general-macetes"
	"theory-inference/instantiation-strategies"
	"theory-inference/existential-matching"
	"theory-inference/general-strategies"
	"theory-inference/unfolding-strategies"
	"theory-inference/induction-strategies"
	"theory-inference/strategy-combining-forms"
	"theory-mechanism/bnf"
	"translations/translations"
	"translations/obligations"
	"translations/translation-builders"
	"translations/transportations"
	"translations/translation-match"
	"translations/language-transportation"
	"translations/theory-transportation"
	"presentation/imps-commands"
	"presentation/imps-special-commands"
	"presentation/indicator-parse-print"
	"presentation/sequence-parse-print"
	"presentation/command-display"
	"presentation/imps-schemeweb")

      )

(convert-source-files 
 (format nil "~A/tea" imps)
 (format nil "~A/oolong" imps)
 *imps-files* "t" "ool")
