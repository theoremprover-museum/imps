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


;
; 			
;			GROUP THEORY EXERCISE
; 
; 
; A group is an algebraic structure consisting of a nonempty set of
; elements, an associative operation on the set, an identity element,
; and an inverse operation.  In this exercise we will begin the
; development of an axiomatic theory of groups named GROUPS.
; 
; 
; 0. Before we can start, we need to load into IMPS some basic
;    mathematics, so load the section of the theory library called
;    FOUNDATION by evaluating

(load-section foundation)

;
; 1. The language of the theory is built by evaluating

(def-language group-language
  (base-types gg)
  (constants
   (e "gg")
   (mul "[gg,gg -> gg]")
   (inv "[gg -> gg]")))

; The language is named GROUP-LANGUAGE.  GG will be the set of group
; elements (formalized as a sort), E the identity element, MUL the
; associative operation, and INV the inverse operation.  The following
; will cause MUL to be parsed as a left associative infix operator and
; printed as an non-associative infix operator:

(def-parse-syntax mul
  (left-method infix-operator-method) 
  (binding 100))

(def-print-syntax mul
  (token " mul ")
  (method present-non-associative-infix-operator)
  (binding 100))

; The theory itself is built by evaluating
   
(def-theory groups
  (language group-language)
  (component-theories h-o-real-arithmetic)
  (axioms
   (left-mul-id 
    "forall(x:gg, e mul x = x)" 
    rewrite)
   (right-mul-id
    "forall(x:gg, x mul e = x)" 
    rewrite)
   (left-mul-inv
    "forall(x:gg, inv(x) mul x = e)" 
    rewrite)
   (right-mul-inv
    "forall(x:gg, x mul inv(x) = e)" 
    rewrite)
   (mul-associativity
    "forall(x,y,z:gg, (x mul y) mul z = x mul (y mul z))" 
    rewrite)))

; The theory is named GROUPS and contains the theory
; H-O-REAL-ARITHMETIC.  The language of the theory includes
; GROUP-LANGUAGE.  The theory has 5 axioms: the first two say E is a
; left and right identity with respect to MUL, respectively; the
; second two say INV returns the left and right inverse of an element
; with respect to MUL, respectively; and the last says MUL is an
; associative operation.  GROUPS contains H-O-REAL-ARITHMETIC so that
; we have the power of real arithmetic available, which allows us to
; express notions such as the cardinality of the set of group
; elements.
;
; Set the current theory to GROUPS using the command found in the
; "General" menu or by evaluaing

(set (current-theory) (name->theory 'groups))

;
; 2. Before doing anything else, it is important to tell the
; domain-range handler of the theory that MUL and INV are total.  To
; do this, prove the two formulas below.  Prove the first by using
; INSISTENT-DIRECT-INFERENCE and then instantiating MUL-ASSOCIATIVITY,
; and similarly prove the second by using INSISTENT-DIRECT-INFERENCE
; and then instantiating LEFT-MUL-INV or RIGHT-MUL-INV.

(def-theorem mul-is-total
  "total_q{mul,[gg,gg -> gg]}"
  (theory groups)
  (usages d-r-convergence)
  (proof 
   (

    insistent-direct-inference
    (instantiate-theorem mul-associativity ("x_0" "x_1" "x_1"))

    )))

(def-theorem inv-is-total
  "total_q{inv,[gg -> gg]}"
  (theory groups)
  (usages d-r-convergence)
  (proof
   (

    insistent-direct-inference
    (instantiate-theorem left-mul-inv ("x_0"))

    )))

; Evaluate these two def-theorem forms after you have proved the
; theorems. The usage D-R-CONVERGENCE is what tells IMPS to install
; these facts into the domain-range handler.
;
; 
; 3. The next thing to do is to add machinery for simplification.  For
; an algebraic theory containing an associative, commutative
; operation, such as a theory of rings or vector spaces, this is done
; primarily by installing an appropriately instantiated algebraic
; processor.  However, a group operation is not necessarily
; commutative, so there is no opportunity to collect like terms.
; Hence, an algebraic processor is not of much use.  Instead, we will
; do simplification in GROUPS by way of a set of rewrite rules.
; 
; Notice that each axiom of GROUPS has been given the usage REWRITE;
; that is, these five axioms will be applied universally when
; simplification is called.  As a test, prove the formula

(view-expr 
  "with(a,b,c:gg, 
     a mul b mul inv(b) mul e mul inv(c) mul c = a)")

; using just the command SIMPLIFY.  Now try to prove the formula

(view-expr 
 "with(a,b,c:gg, 
    b mul inv(b) mul e mul inv(c) mul c mul a = a)")

; using SIMPLIFY.  It seems that MUL-ASSOCIATIVITY is working against
; us as a rewrite rule.  To rectify this situation we need a pair of
; additional rewrite rules.  First, prove

(def-theorem reverse-mul-associativity
  "forall(x,y,z:gg, x mul (y mul z) = (x mul y) mul z)"
  (theory groups)
  (proof 
   (

    simplify

    )))

; Now prove the following formula using REVERSE-MUL-ASSOCIATIVITY and
; LEFT-MUL-INV.

(def-theorem left-inv-cancellation
  "forall(x,y:gg, inv(x) mul (x mul y) = y)"
  (theory groups)
  (usages rewrite)
  (proof
   (

    (apply-macete-with-minor-premises reverse-mul-associativity)
    (apply-macete-with-minor-premises left-mul-inv)
    simplify

    )))

; Prove the next formula by editing the previous proof script.
 
(def-theorem right-inv-cancellation
  "forall(x,y:gg, x mul (inv(x) mul y) = y)"
  (theory groups)
  (usages rewrite)
  (proof
   (

    (apply-macete-with-minor-premises reverse-mul-associativity)
    (apply-macete-with-minor-premises right-mul-inv)
    simplify

    )))

; Now try again to prove

(view-expr 
 "with(a,b,c:gg, 
    b mul inv(b) mul e mul inv(c) mul c mul a = a)")

; We still need some additional rewrite rules to simplify applications
; of INV to compound terms, such as in

(view-expr 
 "with(a,b:gg, 
    inv(inv(inv(a mul inv(a)) mul inv(a mul inv(b)))) = b mul inv(a))")
 
; The following formulas are somewhat tricky to prove.  Try to prove
; one or more of them without looking at the proof scripts.
 
(def-theorem inv-of-e
  "inv(e) = e"
  (theory groups)
  (usages rewrite)
  (proof
   (

    (instantiate-theorem left-mul-id ("inv(e)"))
    (force-substitution "inv(e)" "e mul inv(e)" (0))
    simplify

    )))
  
(def-theorem inv-of-inv
  "forall(x:gg, inv(inv(x)) = x)"
  (theory groups)
  (usages rewrite)
  (proof
   (

    (instantiate-theorem mul-associativity ("inv(inv(x))" "inv(x)" "x"))
    (contrapose "with(p:prop,p)")
    (force-substitution "inv(inv(x)) mul inv(x)" "e" (0))
    (force-substitution "inv(x) mul x" "e" (0))
    simplify
    simplify
    simplify

    )))

(def-theorem push-inv
  "forall(g,h:gg, inv(g mul h) = inv(h) mul inv(g))"
  (theory groups)
  (usages rewrite)
  (proof 
   (

    (instantiate-theorem 
     mul-associativity 
     ("inv(g mul h)" "g mul h" "inv(h) mul inv(g)"))
    (contrapose "with(p:prop,p)")
    (force-substitution "inv(g mul h) mul (g mul h)" "e" (0))
    (force-substitution "(g mul h) mul (inv(h) mul inv(g))" "e" (0))
    simplify
    simplify
    simplify

    )))

; See if SIMPLIFY now works on
 
(view-expr 
 "with(a,b:gg, 
    inv(inv(inv(a mul inv(a)) mul inv(a mul inv(b)))) = b mul inv(a))")

; 
; 4. Prove the left cancellation law for groups by applying
; DIRECT-INFERENCE-STRATEGY and then instantiating MUL-ASSOCIATIVITY.

(def-theorem left-cancellation-law
  "forall(x,y,z:gg, x mul y = x mul z iff y = z)"
  (theory groups)
  (proof
   (

    direct-and-antecedent-inference-strategy
    (instantiate-theorem mul-associativity ("inv(x)" "x" "y"))
    (contrapose 
     "with(y,x:gg,(inv(x) mul x) mul y = inv(x) mul (x mul y))")
    (force-substitution "x mul y" "x mul z" (0))
    (apply-macete-with-minor-premises mul-associativity)
    (apply-macete-with-minor-premises left-inv-cancellation)

    )))

; The proof of the right cancellation law is clearly symmetric to that
; of the left cancellation law.  Often symmetry arguments can be
; formalized in IMPS using a theory interpretation of the theory in
; itself.  That is exactly how we will prove the right cancellation
; law.

; First, we must create the appropriate theory interpretation:

(def-translation mul-reverse
  (source groups)
  (target groups)
  (fixed-theories h-o-real-arithmetic)
  (constant-pairs
    (mul "lambda(x,y:gg, y mul x)"))
  (theory-interpretation-check using-simplification))

; This creates a translation from GROUPS to itself which maps all
; sorts and constants to themselves except for MUL, which is mapped to
; its "reverse".  The THEORY-INTERPRETATION-CHECK argument of the form
; tells IMPS to check off the obligations of the translation using
; simplification.  As we will soon see, MUL-REVERSE will save a lot
; work in developing our theory.
;
; Now, using the command ASSUME-TRANSPORTED-THEOREM with MUL-REVERSE
; and LEFT-CANCELLATION-LAW, prove the right cancellation law, i.e.,

(view-expr "forall(x,y,z:gg, y mul x = z mul x iff y = z )")

; Prove the following trivial left cancellation law:

(def-theorem left-trivial-cancellation-law-left
  "forall(x,y:gg, x = x mul y iff e = y)"
  (theory groups)
  (proof
   (

    (instantiate-theorem left-cancellation-law ("x" "e" "y"))
    simplify
    simplify
    (contrapose "with(y,x:gg,not(x mul e = x mul y))")
    simplify

    )))

; Use the previous theorem to prove this other trivial left
; cancellation law:

(def-theorem left-trivial-cancellation-law-right
  "forall(x,y:gg, x mul y = x iff y = e)"
  (theory groups)
  (proof
   (

    (instantiate-theorem left-trivial-cancellation-law-left ("x" "y"))
    simplify
    simplify

    )))

; Now the right versions of the three left cancellation laws can be
; installed without proof:

(def-theorem right-cancellation-law
  left-cancellation-law
  (theory groups)
  (translation mul-reverse)
  (macete beta-reduce)
  (proof existing-theorem))

(def-theorem right-trivial-cancellation-law-left
  left-trivial-cancellation-law-left
  (theory groups)
  (translation mul-reverse)
  (macete beta-reduce)
  (proof existing-theorem))

(def-theorem right-trivial-cancellation-law-right
  left-trivial-cancellation-law-right
  (theory groups)
  (translation mul-reverse)
  (macete beta-reduce)
  (proof existing-theorem))

; Use these cancellation laws to prove
 
(view-expr 
 "with(a,b,c,d:gg, 
    a mul inv(inv(b) mul inv(c) mul inv(a)) mul b = 
    a mul a mul c mul d mul b mul b implies e = d)")

; You might be tempted to install the cancellation laws as rewrite
; rules.  In general, one should be very conservative in adding
; rewrite rules to a theory since they are applied universally
; whenever simplification is called.  Without care, they can lead to
; undesired simplifications, or worse, to looping.  In IMPS, the
; macete machinery provides a means of extending the simplifier of a
; theory while preserving user control.  For example, the cancellation
; laws can be applied as a unit with the compound macete built by

(def-compound-macete group-cancellation-laws
  (series
   (repeat mul-associativity)
   (repeat left-cancellation-law)
   left-trivial-cancellation-law-left
   left-trivial-cancellation-law-right
   (repeat reverse-mul-associativity)
   (repeat right-cancellation-law)
   right-trivial-cancellation-law-left
   right-trivial-cancellation-law-right))

; This macete performs two steps:
; 
;   (1) It associates fully to the right and applies the left
;       cancellation laws as many times as possible.
; 
;   (2) It associates fully to the left and applies the right
;       cancellation laws as many times as possible.
;
; Now use this macete to again prove

(view-expr 
 "with(a,b,c,d:gg, 
   a mul inv(inv(b) mul inv(c) mul inv(a)) mul b = 
   a mul a mul c mul d mul b mul b 
    implies 
   e = d)")
 
;  
; 5. One of the first concepts defined in a theory of groups is the
; notion of a "subgroup", which is a nonempty set of groups elements
; closed under MUL and INV.  We introduce this concept with:

(def-constant subgroup
  "lambda(a:sets[gg], 
     nonempty_indic_q{a} and
     forall(g,h:gg, ((g in a) and (h in a)) implies ((g mul h) in a)) and
     forall(g:gg, (g in a) implies (inv(g) in a)))"
  (theory groups))

; Every group has at least two subgroups: 
; 
;   (1) The whole set of group elements.
; 
;   (2) The singleton set of the identity element.
; 
; These sets are defined, respectively, with:

(def-constant gg%subgroup 
  "sort_to_indic(gg)" 
  (theory groups))

(def-constant e%subgroup 
  "singleton{e}"
  (theory groups))

; Prove that GG%SUBGROUP and E%SUBGROUP are subgroups.

(def-theorem gg-is-a-subgroup
  "subgroup(gg%subgroup)"
  (theory groups)
  (usages transportable-macete)
  (proof
   (

    unfold-defined-constants
    simplify
    (instantiate-existential ("e"))
    simplify

    )))

(def-theorem singleton-e-is-a-subgroup
  "subgroup(e%subgroup)"
  (theory groups)
  (usages transportable-macete)
  (proof
   (

    unfold-defined-constants
    simplify-insistently
    direct-and-antecedent-inference-strategy
    simplify
    simplify

    )))

; 
; 6. The next form defines a quasi-constructor for asserting that a
; four-tuple with the correct structure is a group:

(def-quasi-constructor group
  "lambda(gg%:sets[gg], mul%:[gg,gg -> gg], e%:gg, inv%:[gg -> gg], 
     forall(x,y:gg, x in gg% and y in gg% implies mul%(x,y) in gg%) and
     e% in gg% and 
     forall(x:gg, x in gg% implies inv%(x) in gg%) and
     forall(x:gg, x in gg% implies mul%(e%,x) = x) and 
     forall(x:gg, x in gg% implies mul%(x,e%) = x) and
     forall(x:gg, x in gg% implies mul%(inv%(x),x) = e%) and 
     forall(x:gg, x in gg% implies mul%(x,inv%(x)) = e%) and
     forall(x,y,z:gg, ((x in gg%) and (y in gg%) and (z in gg%)) implies
       mul%(mul%(x,y),z) = mul%(x,mul%(y,z))))"
  (language groups))

; Prove that subgroups are groups, i.e., prove
 
(view-expr "forall(a:sets[gg], subgroup(a) implies group{a,mul,e,inv})")

; The only thing the least bit hard in the proof is showing that E is
; a member of a subgroup.
;
; The quasi-constructor GROUP provides a way of quantifying over a
; class of group structures in arbitrary theories.  Instead of proving
; group-theoretic results directly about a particular group structure,
; these can be proven in our theory of groups and then transported to
; the theory containing the group structure.
;
;
; 7. In this file we have formalized only a pint-size portion of the
; ocean of concepts and results concerning groups, so there are myriad
; ways to continue the development of group theory in IMPS.  One short
; range goal would be to prove that the cosets of a normal subgroup
; together with the right operations form a group.  This theorem
; requires reasoning about left and right cosets.  Much of the theory
; about cosets can be formulated in terms of the algebraic structure
; called a "group action".  Basic results can be proved about group
; actions, and then applied to all kinds of group action instances
; that naturally occur in group theory (such as the left or right
; translation of a set by a group element).  Hence, a good next step
; would be to develop a basic theory of group actions.  To see this
; approach developed, look at the files in the directory
; "theories/groups/".  They have been organized into sections (small
; collections of related files), as described in the file
; "oolong/theories/some-sections.t".
;
;
; 			   END OF EXERCISE
