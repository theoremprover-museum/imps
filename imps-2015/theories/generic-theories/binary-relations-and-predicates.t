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

(herald binary-relations-and-predicates)


(def-constant BR%REFLEXIVE
  "lambda(r:sets[ind_1,ind_1], 
     forall(x:ind_1, #(r(x,x))))"
  (theory generic-theory-1))

(def-constant BR%SYMMETRIC
  "lambda(r:sets[ind_1,ind_1], 
     forall(x,y:ind_1, #(r(x,y)) implies #(r(y,x))))"
  (theory generic-theory-1))

(def-constant BR%TRANSITIVE
  "lambda(r:sets[ind_1,ind_1], 
     forall(x,y,z:ind_1, #(r(x,y)) and #(r(y,z)) implies #(r(x,z))))"
  (theory generic-theory-1))

(def-constant BR%EQUIV%RELATION
  "lambda(r:sets[ind_1,ind_1], 
     br%reflexive(r) and br%symmetric(r) and br%transitive(r))"
  (theory generic-theory-1))


(def-constant pred%to%rel
  "lambda(p:[ind_1,ind_1 -> prop], 
     lambda(x,y:ind_1, if(p(x,y), an%individual, ?unit%sort)))"
  (theory generic-theory-1))
  

(def-constant equiv%predicate
  "lambda(pred:[ind_1,ind_1 -> prop], br%equiv%relation(pred%to%rel(pred)))"
  (theory generic-theory-1))

(def-theorem characterization-of-equivalence-predicates
  "forall(rel:[ind_1,ind_1 -> prop],
    equiv%predicate(rel) iff
    (forall(a,b,c:ind_1, rel(a,b) and rel(b,c) implies rel(a,c))
        and
     forall(a:ind_1, rel(a,a))
        and
     forall(a,b:ind_1, rel(a,b) implies rel(b,a))))"
  (theory generic-theory-1)
  (proof
   (

    (unfold-single-defined-constant-globally equiv%predicate)
    unfold-defined-constants
    unfold-defined-constants
    (prove-by-logic-and-simplification 0)

    )))