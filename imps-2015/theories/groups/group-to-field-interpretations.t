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

(herald GROUP-TO-FIELD-INTERPRETATIONS)

(include-files
  (files (imps theories/groups/groups)
	 (imps theories/algebra/fields-supplements)))


;;; Obligations

(def-theorem GROUP-TO-FIELD-ADDITIVE-GROUP-OBL-1
  "forall(x:kk,o_kk +_kk x=x)"
  lemma
  (theory fields)
  (proof
   (
    (apply-macete-with-minor-premises commutative-law-for-addition-for-fields)
    (apply-macete-with-minor-premises additive-identity-for-fields)
    )))

(def-theorem GROUP-TO-FIELD-ADDITIVE-GROUP-OBL-2
  "forall(x:kk, -_kk x +_kk x=o_kk)"
  lemma
  (theory fields)
  (proof
   (
    (apply-macete-with-minor-premises commutative-law-for-addition-for-fields)
    (apply-macete-with-minor-premises additive-inverse-for-fields)
    )))

(def-theorem GROUP-TO-FIELD-MULTIPLICATIVE-GROUP-OBL-1
  "not(i_kk=o_kk)"
  lemma
  (theory fields)
  (proof
   (
    (force-substitution "i_kk=o_kk" "o_kk=i_kk" (0))
    (apply-macete-with-minor-premises field-zero-is-not-field-one)
    simplify
    )))

(def-theorem GROUP-TO-FIELD-MULTIPLICATIVE-GROUP-OBL-2
  "forall(x_1,x_0:kk, not(x_0=o_kk) implies x_1=o_kk or not(x_1 *_kk x_0=o_kk))"
  lemma
  (theory fields)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises non-o_kk-is-closed-under-*_kk)
    direct-inference
    )))

(def-theorem GROUP-TO-FIELD-MULTIPLICATIVE-GROUP-OBL-3
  "forall(x:kk, not(x=o_kk) implies if(not(i_kk=o_kk), x, ?kk)=x)"
  lemma
  (theory fields)
  (proof
   (
    (raise-conditional (0))
    direct-and-antecedent-inference-strategy
    )))

(def-theorem GROUP-TO-FIELD-MULTIPLICATIVE-GROUP-OBL-4
  "forsome(x:kk,not(x=o_kk)) implies not(i_kk=o_kk)"
  lemma
  (theory fields)
  (proof
   (
    (apply-macete-with-minor-premises 
     group-to-field-multiplicative-group-obl-1)
    )))

(def-theorem GROUP-TO-FIELD-MULTIPLICATIVE-GROUP-OBL-5
  "forall(x,y,z:kk,
     not(x=o_kk) and not(y=o_kk) and not(z=o_kk)
      implies 
     not(y*x=o_kk) and not(y*z=o_kk))"
  lemma
  (theory fields)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (block
	(script-comment "`direct-and-antecedent-inference-strategy' at (0 0 0 0)")
      (apply-macete-with-minor-premises non-o_kk-is-closed-under-*_kk) 
      simplify)
    (block
	(script-comment "`direct-and-antecedent-inference-strategy' at (0 0 1 0)")
      (apply-macete-with-minor-premises non-o_kk-is-closed-under-*_kk) 
      simplify)
    )))

(def-theorem GROUP-TO-FIELD-MULTIPLICATIVE-GROUP-OBL-5-PERMUTED
  "forall(x,y,z:kk,
     not(x=o_kk) and not(y=o_kk) and not(z=o_kk)
   implies 
     not(y *_kk x=o_kk) and not(z *_kk y=o_kk))"
  lemma
  (theory fields)
  (proof
   (
    (assume-theorem group-to-field-multiplicative-group-obl-5)
    direct-inference
    (instantiate-universal-antecedent "with(p:prop,p);" ("x" "y" "z"))
    (move-to-ancestor 3)
    (incorporate-antecedent "with(p:prop,p);")
    simplify
    )))


;;; Interpretations

(def-translation GROUP-TO-FIELD-ADDITIVE-GROUP
  (source groups)
  (target fields)
  (fixed-theories h-o-real-arithmetic)
  (sort-pairs
   (gg kk))
  (constant-pairs
   (e o_kk)
   (mul +_kk)
   (inv -_kk))
  (theory-interpretation-check using-simplification))

(def-translation GROUP-TO-FIELD-MULTIPLICATIVE-GROUP
  (source groups)
  (target fields)
  (fixed-theories h-o-real-arithmetic)
  (sort-pairs
   (gg (pred "lambda(z:kk,not(z=o_kk))")))
  (constant-pairs
   (e i_kk)
   (mul "lambda(x,y:kk,if(not(x=o_kk) and not(y=o_kk), x *_kk y, ?kk))")
   (inv "lambda(x:kk,if(not(x=o_kk), inv(x), ?kk))"))  
  (theory-interpretation-check using-simplification))

