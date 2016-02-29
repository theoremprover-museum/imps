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


(herald induction-in-cpos)

(def-theorem induction-in-cpos
  "forall(s:sets[uu],a:uu,
     a in s
      and 
     forall(t:sets[uu],
       a in t and t subseteq s and #(prec%sup(t)) implies 
       prec%sup(t) in s)
      and 
     forall(y,z:uu,
       y in s and a prec y and y prec z and not(z=y)
        implies 
       forsome(y_0:uu,
         y_0 in s and y_0 prec z and y prec y_0 and not(y=y_0)))
      implies 
     forall(x:uu,a prec x implies x in s))"
  (theory complete-partial-order)
  (usages transportable-macete)
  (proof
   (


    direct-and-antecedent-inference-strategy
    (script-comment "After breaking up the logical structure of the expression, we
                    have to show that a fixed x belongs to s provided the assumptions
                    on s hold and a prec s.")
    (instantiate-universal-antecedent "with(p:prop,forall(t:sets[uu],p));"
				      ("indic{w:uu, w in s and a prec w and w prec x}"))
    (block
     (script-comment "Contraposition to show antecedent of instantiated assumption holds.")
     (contrapose "with(p:prop,not(p));")
     simplify-insistently
     (apply-macete-with-minor-premises prec-reflexivity)
     )
    (block
     (script-comment "Contraposition for a similar reason.")
     (contrapose "with(x_$0:uu,f:[uu,prop],x_$0 in pred_to_indic(f));")
     simplify-insistently)
    (block 
     (contrapose "with(p:prop,not(p));")
     (apply-macete-with-minor-premises prec%sup-defined)
     direct-and-antecedent-inference-strategy
     (instantiate-existential ("a"))
     (unfold-single-defined-constant (0) prec%majorizes)
     simplify-insistently
     (instantiate-existential ("x")))

    (block

     (instantiate-universal-antecedent "with(p:prop,forall(y,z:uu,p));"
				       ("prec%sup(indic{w:uu,  w in s and a prec w and w prec x})" "x"))
     (contrapose "with(p:prop,not(p));")

     (apply-macete-with-minor-premises minorizes-property-of-prec%sup)
     simplify-insistently
     (instantiate-existential ("a"))
     (apply-macete-with-minor-premises prec-reflexivity)
     (contrapose "with(p:prop,not(p));")
     (apply-macete-with-minor-premises lub-property-of-prec%sup)
     direct-and-antecedent-inference-strategy
     (unfold-single-defined-constant-globally prec%majorizes)
     simplify-insistently
     simplify
     (contrapose "with(p:prop,not(p));")
     (apply-macete-with-minor-premises prec-anti-symmetry)
     direct-and-antecedent-inference-strategy
     (apply-macete-with-minor-premises minorizes-property-of-prec%sup)
     direct-and-antecedent-inference-strategy
     (instantiate-existential ("y_$0"))
     simplify-insistently
     (apply-macete-with-minor-premises prec-transitivity)
     (instantiate-existential ("prec%sup(indic{w:uu,  w in s and a prec w and w prec x})"))
     (apply-macete-with-minor-premises minorizes-property-of-prec%sup)
     direct-and-antecedent-inference-strategy
     simplify-insistently
     (instantiate-existential ("a"))
     (apply-macete-with-minor-premises prec-reflexivity)
     (apply-macete-with-minor-premises prec-reflexivity)

     )
    )))



;;;(def-theorem induction-in-cpos
;;;  "forall(s:sets[uu],a:uu,
;;;          forall(x:uu,a prec x implies x in s)
;;;             iff
;;;   (
;;;     a in s
;;;      and 
;;;     forall(t:sets[uu],
;;;       nonempty_indic_q{t} and t subseteq s and #(prec%sup(t)) implies 
;;;       prec%sup(t) in s)
;;;      and 
;;;     forall(y,z:uu,
;;;       y in s and a prec y and y prec z and not(z=y)
;;;        implies 
;;;       forsome(y_0:uu,
;;;         y_0 in s and y_0 prec z and y prec y_0 and not(y=y_0)))))"
;;;  (theory complete-partial-order))


(def-theorem induction-principle-for-cpos
  "forall(p:[uu,prop],a,b:uu,
     a prec b
      implies 
     forall(x:uu,a prec x and x prec b implies p(x))
      iff 
     (p(a)
      and 
     (forall(t:sets[uu],
        a in t
         and 
        t subseteq indic{x:uu,  a prec x and x prec b and p(x)}
         implies 
        p(prec%sup(t)))
      and 
     forall(y,z:uu,
       p(y) and a prec y and y prec z and not(z=y) and z prec b
        implies 
       forsome(y_0:uu,
         p(y_0) and y_0 prec z and y prec y_0 and not(y=y_0))))))"  
  (theory complete-partial-order)
  (usages transportable-macete)
  (proof
   (


    direct-and-antecedent-inference-strategy
    (backchain "with(p:prop,forall(x:uu,p));")
    direct-inference
    (apply-macete-with-minor-premises prec-reflexivity)
    (cut-with-single-formula "#(prec%sup(t))")
    (move-to-sibling 1)
    (apply-macete-with-minor-premises prec%sup-defined)
    direct-and-antecedent-inference-strategy
    (instantiate-existential ("a"))
    (instantiate-existential ("b"))
    (unfold-single-defined-constant (0) prec%majorizes)
    direct-and-antecedent-inference-strategy
    (incorporate-antecedent "with(f,t:sets[uu],t subseteq f);")
    simplify-insistently
    (backchain "forall(x:uu,
			 with(p:prop,p and p) implies with(p:[uu,prop],p(x)));")
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises minorizes-property-of-prec%sup)
    direct-inference
    (instantiate-existential ("a"))
    (apply-macete-with-minor-premises lub-property-of-prec%sup)
    direct-and-antecedent-inference-strategy
    (unfold-single-defined-constant (0) prec%majorizes)
    direct-and-antecedent-inference-strategy
    (incorporate-antecedent "with(f,t:sets[uu],t subseteq f);")
    simplify-insistently
    (instantiate-existential ("z"))
    (backchain "with(p:prop,forall(x:uu,p));")
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises prec-transitivity)
    (instantiate-existential ("y"))
    (apply-macete-with-minor-premises prec-reflexivity)
    simplify
    (script-comment "this ends the proof in one direction.")
    (cut-with-single-formula "x in indic{x:uu, a prec x and (x prec b implies p(x))}")
    (incorporate-antecedent "with(x:uu,f:sets[uu],x in f);")
    simplify-insistently
    (apply-macete-with-minor-premises induction-in-cpos)
    simplify-insistently
    (instantiate-existential ("a"))
    (apply-macete-with-minor-premises prec-reflexivity)
    (apply-macete-with-minor-premises minorizes-property-of-prec%sup)
    direct-inference
    (instantiate-existential ("a"))
    (backchain "with(p:prop,forall(t:sets[uu],p));")
    direct-and-antecedent-inference-strategy
    simplify-insistently
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises prec-transitivity)
    (instantiate-existential ("prec%sup(t_$1)"))
    (apply-macete-with-minor-premises minorizes-property-of-prec%sup)
    direct-and-antecedent-inference-strategy
    (instantiate-existential ("x_$0"))
    (apply-macete-with-minor-premises prec-reflexivity)
    (backchain "with(p:prop,p and p and p);")
    direct-and-antecedent-inference-strategy
    (instantiate-universal-antecedent "with(p:prop,forall(y,z:uu,p));"
				       ("y_$3" "z_$1"))
    (instantiate-existential ("z_$1"))
    (apply-macete-with-minor-premises prec-transitivity)
    (instantiate-existential ("y_$3"))
    (antecedent-inference-strategy (3))
    (contrapose "with(b,y_$3:uu,not(y_$3 prec b));")
    (apply-macete-with-minor-premises prec-transitivity)
    (instantiate-existential ("z_$1"))
    (apply-macete-with-minor-premises prec-reflexivity)
    simplify
    (instantiate-existential ("z_$1"))
    (apply-macete-with-minor-premises prec-transitivity)
    (instantiate-existential ("y_$3"))
    (apply-macete-with-minor-premises prec-reflexivity)
    simplify
    (instantiate-existential ("y_0"))
    (apply-macete-with-minor-premises prec-transitivity)
    (instantiate-existential ("y_$3"))       

    ))


  )
