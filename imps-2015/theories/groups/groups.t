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


(herald GROUPS)

(load-section foundation)



;;; Parsing and printing

(def-parse-syntax mul
  (left-method infix-operator-method) 
  (binding 100))

(def-print-syntax mul
  (token " mul ")
  (method present-non-associative-infix-operator) 
  (binding 100))


;;; Group theory

(def-language GROUP-LANGUAGE
  (base-types gg)
  (constants
   (e "gg")
   (mul "[gg,gg,gg]")
   (inv "[gg,gg]")))

(def-theory GROUPS
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


;;; Group quasi-constructor

(def-quasi-constructor GROUP
  "lambda(gg%:sets[gg], mul%:[gg,gg,gg], e%:gg, inv%:[gg,gg], 
     forall(x,y:gg, x in gg% and y in gg% implies mul%(x,y) in gg%) and
     e% in gg% and 
     forall(x:gg, x in gg% implies inv%(x) in gg%) and
     forall(x:gg, x in gg% implies mul%(e%,x)=x) and 
     forall(x:gg, x in gg% implies mul%(x,e%)=x) and
     forall(x:gg, x in gg% implies mul%(inv%(x),x)=e%) and 
     forall(x:gg, x in gg% implies mul%(x,inv%(x))=e%) and
     forall(x,y,z:gg, ((x in gg%) and (y in gg%) and (z in gg%)) implies
       mul%(mul%(x,y),z) = mul%(x,mul%(y,z))))"
  (language groups))


;;; Preliminary lemmas

(def-theorem MUL-IS-TOTAL
  "total_q{mul,[gg,gg,gg]}"
  (theory groups)
  (usages d-r-convergence transportable-macete)
  (proof 
   (
    insistent-direct-inference
    (instantiate-theorem mul-associativity ("x_0" "x_1" "x_1"))
    )))

(def-theorem INV-IS-TOTAL
  "total_q{inv,[gg,gg]}"
  (theory groups)
  (usages d-r-convergence transportable-macete)
  (proof
   (
    insistent-direct-inference
    (instantiate-theorem left-mul-inv ("x_0"))
    )))

(def-theorem REVERSE-MUL-ASSOCIATIVITY
  "forall(x,y,z:gg, x mul (y mul z) = (x mul y) mul z)"
  (theory groups)
  (usages transportable-macete)
  (proof (simplify)))


;;; Rewrite rules

(def-theorem LEFT-INV-CANCELLATION
  "forall(x,y:gg, inv(x) mul (x mul y) = y)"
  (theory groups)
  (usages rewrite transportable-macete)
  (proof
   (
    (apply-macete-with-minor-premises reverse-mul-associativity)
    (apply-macete-with-minor-premises left-mul-inv)
    simplify
    )))

(def-theorem RIGHT-INV-CANCELLATION
  "forall(x,y:gg, x mul (inv(x) mul y) = y)"
  (theory groups)
  (usages rewrite transportable-macete)
  (proof  ;; Obtained by editing the previous proof script
   (
    (apply-macete-with-minor-premises reverse-mul-associativity)
    (apply-macete-with-minor-premises right-mul-inv)
    simplify
    )))

;; The previous two theorems can be proved with the following script:

(def-script INV-CANCELLATION-SCRIPT 1
  ;; $1 is a symbol
  (
   (apply-macete-with-minor-premises reverse-mul-associativity)
   (apply-macete-with-minor-premises $1)
   simplify
   ))

(def-theorem INV-OF-E
  "inv(e)=e"
  (theory groups)
  (usages rewrite transportable-macete)
  (proof
   (
    (instantiate-theorem left-mul-id ("inv(e)"))
    (force-substitution "inv(e)" "e mul inv(e)" (0))
    simplify
    )))

(def-theorem INV-OF-INV
  "forall(x:gg, inv(inv(x))=x)"
  (theory groups)
  (usages rewrite transportable-macete)
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

(def-theorem PUSH-INV
  "forall(g,h:gg, inv(g mul h) = inv(h) mul inv(g))"
  (theory groups)
  (usages rewrite transportable-macete)
  (proof 
   (
    (instantiate-theorem mul-associativity 
			 ("inv(g mul h)" "g mul h" "inv(h) mul inv(g)"))
    (contrapose "with(p:prop,p)")
    (force-substitution "inv(g mul h) mul (g mul h)" "e" (0))
    (force-substitution "(g mul h) mul (inv(h) mul inv(g))" "e" (0))
    simplify
    simplify
    simplify
    )))


;;; Mul reverse theory interpretation

(def-translation MUL-REVERSE
  (source groups)
  (target groups)
  (fixed-theories h-o-real-arithmetic)
  (constant-pairs
   (mul "lambda(x,y:gg, y mul x)"))
  force-under-quick-load
  (theory-interpretation-check using-simplification))


;;;  Cancellation laws

(def-theorem LEFT-CANCELLATION-LAW
  "forall(x,y,z:gg, x mul y = x mul z iff y=z)"
  (theory groups)
  (usages transportable-macete)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (instantiate-theorem mul-associativity ("inv(x)" "x" "y"))
    (contrapose "with(y,x:gg,(inv(x) mul x) mul y=inv(x) mul (x mul y))")
    (force-substitution "x mul y" "x mul z" (0))
    (apply-macete-with-minor-premises mul-associativity)
    (apply-macete-with-minor-premises left-inv-cancellation)
    )))

(def-theorem LEFT-TRIVIAL-CANCELLATION-LAW-LEFT
  "forall(x,y:gg, x = x mul y iff e=y)"
  (theory groups)
  (usages transportable-macete)
  (proof
   (
    (instantiate-theorem left-cancellation-law ("x" "e" "y"))
    simplify
    simplify
    (contrapose "with(y,x:gg,not(x mul e=x mul y))")
    simplify
    )))

(def-theorem LEFT-TRIVIAL-CANCELLATION-LAW-RIGHT
  "forall(x,y:gg, x mul y = x iff y=e)"
  (theory groups)
  (usages transportable-macete)
  (proof
   (
    (instantiate-theorem left-trivial-cancellation-law-left ("x" "y"))
    simplify
    simplify
    )))

(def-theorem RIGHT-CANCELLATION-LAW
  ;; "forall(x,y,z:gg, y mul x=z mul x iff y=z)"
  left-cancellation-law
  (theory groups)
  (usages transportable-macete)
  (translation mul-reverse)
  (proof existing-theorem))

(def-theorem RIGHT-TRIVIAL-CANCELLATION-LAW-LEFT
  ;; "forall(x,y:gg, x=y mul x iff e=y)"
  left-trivial-cancellation-law-left
  (theory groups)
  (usages transportable-macete)
  (translation mul-reverse)
  (proof existing-theorem))

(def-theorem RIGHT-TRIVIAL-CANCELLATION-LAW-RIGHT
  ;; "forall(x,y:gg, y mul x=x iff y=e)"
  left-trivial-cancellation-law-right
  (theory groups)
  (usages transportable-macete)
  (translation mul-reverse)
  (proof existing-theorem))

(def-compound-macete GROUP-CANCELLATION-LAWS
  (series
   (repeat mul-associativity)
   (repeat left-cancellation-law)
   left-trivial-cancellation-law-left
   left-trivial-cancellation-law-right
   (repeat reverse-mul-associativity)
   (repeat right-cancellation-law)
   right-trivial-cancellation-law-left
   right-trivial-cancellation-law-right))

