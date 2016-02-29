;% Copyright (c) 1990-1994 The MITRE Corporation
;% 
;% Authors: W. M. Farmer, J. D. Guttman, F. J. Thayer
;%   
;% The MITRE Corporation (MITRE) provides this software to you without
;% charge to use, copy, modify or enhance for any legitimate purpose
;% provided you reproduce MITRE's copyright notice in any copy or
;% derivative work of this software.
;% 
;% This software is the copyright work of MITRE.  No ownership or other
;% proprietary interest in this software is granted you other than what
;% is granted in this license.
;% 
;% Any modification or enhancement of this software must identify the
;% part of this software that was modified, by whom and when, and must
;% inherit this license including its warranty disclaimers.
;% 
;% MITRE IS PROVIDING THE PRODUCT "AS IS" AND MAKES NO WARRANTY, EXPRESS
;% OR IMPLIED, AS TO THE ACCURACY, CAPABILITY, EFFICIENCY OR FUNCTIONING
;% OF THIS SOFTWARE AND DOCUMENTATION.  IN NO EVENT WILL MITRE BE LIABLE
;% FOR ANY GENERAL, CONSEQUENTIAL, INDIRECT, INCIDENTAL, EXEMPLARY OR
;% SPECIAL DAMAGES, EVEN IF MITRE HAS BEEN ADVISED OF THE POSSIBILITY OF
;% SUCH DAMAGES.
;% 
;% You, at your expense, hereby indemnify and hold harmless MITRE, its
;% Board of Trustees, officers, agents and employees, from any and all
;% liability or damages to third parties, including attorneys' fees,
;% court costs, and other related costs and expenses, arising out of your
;% use of this software irrespective of the cause of said liability.
;% 
;% The export from the United States or the subsequent reexport of this
;% software is subject to compliance with United States export control
;% and munitions control restrictions.  You agree that in the event you
;% seek to export this software or any derivative work thereof, you
;% assume full responsibility for obtaining all necessary export licenses
;% and approvals and for assuring compliance with applicable reexport
;% restrictions.
;% 
;% 
;% COPYRIGHT NOTICE INSERTED: Mon Apr 11 11:42:27 EDT 1994


(herald PURE-GENERIC-THEORIES-WITH-SUBSORT)

(load-section generic-theories)
(load-section mappings)

(def-language PURE-GENERIC-LANGUAGE-1-WITH-1-SUBSORT
  (embedded-language pure-generic-language-1)
  (sorts (uu_1 ind_1)))

(def-language PURE-GENERIC-LANGUAGE-2-WITH-2-SUBSORTS
  (embedded-language pure-generic-language-2)
  (sorts (uu_1 ind_1) (uu_2 ind_2)))

(def-theory PURE-GENERIC-THEORY-1-WITH-1-SUBSORT
  (language pure-generic-language-1-with-1-subsort)
  (component-theories pure-generic-theory-1))

(def-theory PURE-GENERIC-THEORY-2-WITH-1-SUBSORT
  (language pure-generic-language-1-with-1-subsort)
  (component-theories pure-generic-theory-2))

(def-theory PURE-GENERIC-THEORY-2-WITH-2-SUBSORTS
  (language pure-generic-language-2-with-2-subsorts)
  (component-theories pure-generic-theory-2))

(def-theory PURE-GENERIC-THEORY-3-WITH-2-SUBSORTS
  (language pure-generic-language-2-with-2-subsorts)
  (component-theories pure-generic-theory-3))


;; Lemmas

(def-theorem SURJECTIVE-INVERSE-WITH-SUBSORT
  "forall(a:sets[ind_1],f:[uu_1,ind_2],
     injective_on_q(f,a) and dom(f)=a 
      implies 
     surjective_on_q{inverse{f},ran{f},a})"
  (theory pure-generic-theory-2-with-1-subsort)
  (usages transportable-macete)
  (proof
   (

    direct-and-antecedent-inference-strategy
    insistent-direct-and-antecedent-inference-strategy
    (block 
     (script-comment 
      "`insistent-direct-and-antecedent-inference-strategy' at (0)")
     (apply-macete-with-minor-premises tr%dom-of-inverse)
     (apply-macete-with-minor-premises tr%injective-iff-injective-on-domain)
     simplify)
    (block 
     (script-comment 
      "`insistent-direct-and-antecedent-inference-strategy' at (1)")
     (backchain-backwards "with(a:sets[ind_1],f:sets[uu_1],f=a);")
     extensionality
     direct-inference
     (case-split ("#(x_0,uu_1)"))
     (block 
      (script-comment "`case-split' at (1)")
      beta-reduce-repeatedly
      (raise-conditional (1))
      simplify
      direct-and-antecedent-inference-strategy
      (block 
       (script-comment 
	"`direct-and-antecedent-inference-strategy' at (0 0 0 0)")
       (cut-with-single-formula "x_0=iota(y:uu_1,f(y)=x_$4) and x_0=x_0")
       (incorporate-antecedent "with(u:uu_1,x_0:ind_1,x_0=u);")
       (eliminate-defined-iota-expression 0 w)
       simplify)
      (block 
       (script-comment "`direct-and-antecedent-inference-strategy' at (0 1 1)")
       (instantiate-existential ("f(x_0)"))
       (eliminate-iota 0)
       (instantiate-existential ("x_0"))
       (instantiate-universal-antecedent 
	"with(f:[uu_1,ind_2],a:sets[ind_1],injective_on_q{f,a});"
	("z%iota_$0" "x_0"))
       (block 
	(script-comment "`instantiate-universal-antecedent' at (0 0 0 0)")
	(contrapose "with(p:prop,not(p));")
	(backchain-backwards "with(a:sets[ind_1],f:sets[uu_1],f=a);")
	beta-reduce-insistently
	simplify)
       (block 
	(script-comment "`instantiate-universal-antecedent' at (0 0 0 1)")
	(contrapose "with(p:prop,not(p));")
	(backchain-backwards "with(a:sets[ind_1],f:sets[uu_1],f=a);")
	beta-reduce-insistently
	simplify)))
     (block 
      (script-comment "`case-split' at (2)")
      insistent-direct-and-antecedent-inference-strategy
      (contrapose "with(p:prop,not(p));")
      (incorporate-antecedent "with(x_0:ind_1,f:sets[ind_1],x_0 in f);")
      beta-reduce-insistently
      simplify
      direct-and-antecedent-inference-strategy))

    )))
