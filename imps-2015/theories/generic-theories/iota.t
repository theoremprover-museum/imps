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

(herald IOTA)

(include-files
 (files (imps theories/generic-theories/pure-generic-theories)))


;;; Properties of defined iota expressions

(def-theorem DEFINED-IOTA-EXPRESSION
  "forall(p:[ind_1,prop], 
     #(iota(i:ind_1,p(i))) 
       implies
     (p(iota(i:ind_1,p(i))) and 
     forall(j:ind_1, p(j) implies j=iota(i:ind_1,p(i)))))"
  (theory pure-generic-theory-1)
  (usages transportable-macete)
  (proof
   (

    direct-inference
    direct-inference
    (cut-with-single-formula 
     "#(iota(i:ind_1,p(i))) and forall(x:ind_1,x=x)")
    (contrapose "with(i:ind_1,#(i));")
    (eliminate-iota 0)
    direct-and-antecedent-inference-strategy
    (contrapose "with(p:prop,p or p);")
    direct-inference
    (block 
      (script-comment "`direct-inference' at (0)")
      (eliminate-iota 0)
      (instantiate-existential ("y%iota")))
    (block 
      (script-comment "`direct-inference' at (1)")
      (instantiate-universal-antecedent-multiply 
       "with(y%iota:ind_1,p:[ind_1,prop],
         forall(z%iota:ind_1,p(z%iota) implies z%iota=y%iota));"
       (("j") ("iota(i:ind_1,p(i))")))
      direct-inference
      direct-inference)

    )))

(def-theorem DEFINED-IOTA-EXPRESSION-SATISFIABILITY
  "forall(p:[ind_1,prop], 
     #(iota(i:ind_1,p(i))) implies p(iota(i:ind_1,p(i))))"
  (theory pure-generic-theory-1)
  (usages transportable-macete)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (instantiate-theorem defined-iota-expression ("p"))
    )))

(def-theorem DEFINED-IOTA-EXPRESSION-EXISTENCE
  "forall(p:[ind_1,prop], 
     #(iota(i:ind_1,p(i))) implies nonvacuous_q{p})"
  (theory pure-generic-theory-1)
  (usages transportable-macete)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (instantiate-theorem defined-iota-expression ("p"))
    auto-instantiate-existential
    )))

(def-theorem DEFINED-IOTA-EXPRESSION-FULL-EXISTENCE
  "forall(%%p%%:[ind_1,prop], 
     not(#(iota(i:ind_1,%%p%%(i)))) 
      or
     forsome(j:ind_1, 
       j=iota(i:ind_1,%%p%%(i)) and %%p%%(j) and forall(j_1:ind_1, %%p%%(j_1) 
        implies 
       j=j_1)))"
  (theory pure-generic-theory-1)
  (usages transportable-macete)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (instantiate-theorem defined-iota-expression ("%%p%%"))
    auto-instantiate-existential
    (instantiate-universal-antecedent 
     "with(%%p%%:prop, forall(j:ind_1,%%p%%))" ("j_$0"))
    )))

(def-theorem DEFINED-IOTA-EXPRESSION-UNIQUENESS
  "forall(p:[ind_1,prop], 
     #(iota(i:ind_1,p(i))) 
        implies
     forall(j:ind_1, p(j) implies j=iota(i:ind_1,p(i))))"
  (theory pure-generic-theory-1)
  (usages transportable-macete)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (instantiate-theorem defined-iota-expression ("p"))
    (backchain "with(p,q:prop, forall(j:ind_1, p implies q))")
    )))

(def-theorem DEFINED-IOTA-EXPRESSION-IOTA-FREE-UNIQUENESS
  "forall(p:[ind_1,prop], 
     #(iota(i:ind_1,p(i))) 
       implies
     forall(i,j:ind_1, (p(i) and p(j)) implies i=j))"
  (theory pure-generic-theory-1)
  (usages transportable-macete)
  (proof
   (

    direct-and-antecedent-inference-strategy
    (instantiate-theorem defined-iota-expression ("p"))
    (instantiate-universal-antecedent-multiply 
     "with(p:prop,forall(j:ind_1,p));"
     (("i") ("j")))

    )))


;;; Equal iota expressions

(def-theorem EQUAL-IOTA-EXPRESSIONS-LEMMA
  "forall(p,q:[ind_1,prop], 
     iota(i:ind_1,p(i)) = iota(i:ind_1,q(i)) 
       implies
     forall(k:ind_1, p(k) implies q(k)))"
  lemma
  (theory pure-generic-theory-1)
  (usages transportable-macete)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (instantiate-theorem defined-iota-expression-uniqueness ("p"))
    (instantiate-universal-antecedent "with(p:prop, forall(j:ind_1,p))" ("k"))
    (force-substitution "k" "iota(i:ind_1,q(i))" (0))
    (apply-macete-with-minor-premises defined-iota-expression-satisfiability)
    )))

(def-theorem EQUAL-IOTA-EXPRESSIONS
  "forall(p,q:[ind_1,prop], 
     iota(i:ind_1,p(i)) = iota(i:ind_1,q(i)) implies p=q)"
  (theory pure-generic-theory-1)
  (usages transportable-macete)
  (proof
   (
    direct-and-antecedent-inference-strategy
    extensionality
    direct-inference
    simplify
    (instantiate-theorem equal-iota-expressions-lemma ("p" "q"))
    (instantiate-theorem equal-iota-expressions-lemma ("q" "p"))
    (instantiate-universal-antecedent 
     "with(p,q:[ind_1,prop],forall(k:ind_1,q(k) implies p(k)));" ("x_0"))
    (instantiate-universal-antecedent 
     "with(q,p:[ind_1,prop],forall(k:ind_1,p(k) implies q(k)));" ("x_0"))
    simplify
    simplify
    )))


;;; Elimination of defined iota expressions

(def-theorem DEFINED-IOTA-EXPRESSION-ELIMINATION
  "forall(p:[ind_1,prop], 
     #(iota(i:ind_1,p(i))) 
       iff 
     forsome(i:ind_1, p(i) and forall(j:ind_1, p(j) implies j=i)))"
  (theory pure-generic-theory-1)
  (usages transportable-macete)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (instantiate-theorem defined-iota-expression-full-existence ("p"))
    (instantiate-existential ("j"))
    (instantiate-universal-antecedent 
     "with(p:prop, forall(j_1:ind_1,p))" ("j_$0"))
    (eliminate-iota 0)
    auto-instantiate-existential
    direct-and-antecedent-inference-strategy
    (instantiate-theorem defined-iota-expression-full-existence ("p"))
    (instantiate-existential ("j"))
    (instantiate-universal-antecedent 
     "with(p:prop, forall(j_1:ind_1,p))" ("j_$0"))
    )))

(def-theorem NEGATED-DEFINED-IOTA-EXPRESSION-ELIMINATION-1
  "forall(p:[ind_1,prop], 
     forall(i:ind_1, not(p(i))) 
      implies 
     not(#(iota(i:ind_1,p(i)))))"
  (theory pure-generic-theory-1)
  (usages transportable-macete)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (eliminate-iota 0)
    direct-and-antecedent-inference-strategy
    (contrapose "with(p:[ind_1,prop],forall(i:ind_1,not(p(i))));")
    auto-instantiate-existential
    )))

(def-theorem NEGATED-DEFINED-IOTA-EXPRESSION-ELIMINATION-2
  "forall(p:[ind_1,prop], 
     forsome(i,j:ind_1, p(i) and p(j) and not(i=j))
      implies 
     not(#(iota(i:ind_1,p(i)))))"
  (theory pure-generic-theory-1)
  (usages transportable-macete)
  (proof
   (

    direct-and-antecedent-inference-strategy
    (eliminate-iota 0)
    direct-and-antecedent-inference-strategy
    (contrapose "with(p:prop,not(p));")
    (instantiate-universal-antecedent-multiply 
     "with(y%iota:ind_1,p:[ind_1,prop],
        forall(z%iota:ind_1,p(z%iota) implies z%iota=y%iota));"
     (("i") ("j")))

    )))

(def-theorem NEGATED-DEFINED-IOTA-EXPRESSION-ELIMINATION
  "forall(p:[ind_1,prop], 
     not(#(iota(i:ind_1,p(i)))) 
       iff 
     (forall(i:ind_1, 
        not(p(i))) 
         or 
        forsome(i,j:ind_1, p(i) and p(j) and not(i=j))))"
  (theory pure-generic-theory-1)
  (usages transportable-macete)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (contrapose "with(p:[ind_1,prop],not(#(iota(i:ind_1,p(i)))));")
    (eliminate-iota 0)
    auto-instantiate-existential
    (backchain "with(p:prop, forall(i,j:ind_1,p))")
    simplify
    (apply-macete-with-minor-premises 
     negated-defined-iota-expression-elimination-1)
    (apply-macete-with-minor-premises 
     negated-defined-iota-expression-elimination-2)
    auto-instantiate-existential
    )))


;;; Elimination of iota expression equations

(def-theorem LEFT-IOTA-EXPRESSION-EQUATION-ELIMINATION
  "forall(a:ind_1,p:[ind_1,prop], 
     iota(i:ind_1,p(i)) = a iff (p(a) and forall(b:ind_1, p(b) implies b=a)))"
  (theory pure-generic-theory-1)
  (usages transportable-macete)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (force-substitution "a" "iota(i:ind_1,p(i))" (0))
    (apply-macete-with-minor-premises 
     defined-iota-expression-satisfiability)
    (apply-macete-with-minor-premises 
     defined-iota-expression-iota-free-uniqueness)
    auto-instantiate-existential
    (eliminate-iota 0)
    auto-instantiate-existential
    )))

(def-theorem RIGHT-IOTA-EXPRESSION-EQUATION-ELIMINATION
  "forall(a:ind_1,p:[ind_1,prop], 
     a = iota(i:ind_1,p(i)) iff (p(a) and forall(b:ind_1, p(b) implies b=a)))"
  (theory pure-generic-theory-1)
  (usages transportable-macete)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (force-substitution "a" "iota(i:ind_1,p(i))" (0))
    (apply-macete-with-minor-premises 
     defined-iota-expression-satisfiability)
    (apply-macete-with-minor-premises 
     defined-iota-expression-iota-free-uniqueness)
    auto-instantiate-existential
    (eliminate-iota 0)
    auto-instantiate-existential
    )))


;;; Macetes

(def-schematic-macete TR%ABSTRACTION-FOR-IOTA-BODY
  "with(body:prop, 
     iota(i:ind_1,body) == iota(i:ind_1,lambda(i:ind_1,body)(i)))"
  null
  transportable
  (theory pure-generic-theory-1))

(def-compound-macete IOTA-ABSTRACTION-MACETE
  (sound
   tr%abstraction-for-iota-body
   beta-reduce-unstoppably
   beta-reduce-unstoppably))

(def-schematic-macete TR%ABSTRACTION-FOR-FORSOME-BODY
  "with(body:prop, 
     forsome(i:ind_1,body) iff forsome(i:ind_1,lambda(i:ind_1,body)(i)))"
  null
  transportable
  (theory pure-generic-theory-1))

(def-compound-macete ELIMINATE-IOTA-MACETE
  (sequential
   iota-abstraction-macete
   (series
    tr%defined-iota-expression-elimination
    tr%negated-defined-iota-expression-elimination
    tr%left-iota-expression-equation-elimination
    tr%right-iota-expression-equation-elimination)
   beta-reduce))

(def-compound-macete ELIMINATE-FORSOME-MACETE
  (sequential
   (sound
    tr%abstraction-for-forsome-body
    beta-reduce-unstoppably
    beta-reduce-unstoppably)
   tr%defined-iota-expression-existence
   beta-reduce))


