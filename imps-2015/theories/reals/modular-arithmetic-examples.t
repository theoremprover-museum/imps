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


(herald modular-arithmetic-examples)

(include-files 
 (files (imps theories/reals/modular-arithmetic)))

(def-theorem add-one-typical-case
  "forall(x:zz_mod, x<modulus-1 implies +_mod(x,1)=x+1)"
  (theory arithmetic-mod-n)
  (proof
   (

    (unfold-single-defined-constant (0) +_mod)
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises mod-characterization)
    simplify
    (cut-with-single-formula "#(x,zz_mod)")
    (incorporate-antecedent "with(x:zz_mod,#(x,zz_mod));")
    (apply-macete-with-minor-premises zz_mod-defining-axiom_arithmetic-mod-n)
    (unfold-single-defined-constant (0) divides)
    simplify

    )))

(def-theorem add-one-special-case
  "forall(x:zz_mod, +_mod(modulus-1,1)=0)"
  (theory arithmetic-mod-n)
  (proof
   (

    
    (unfold-single-defined-constant (0) +_mod)
    simplify
    (apply-macete-with-minor-premises mod-characterization)
    (unfold-single-defined-constant (0) divides)
    simplify
    )))

(def-theorem ()
  "#(-_mod(1))"
  (theory arithmetic-mod-n)
  lemma
  (proof
   (
    (apply-macete-with-minor-premises -_mod-computation-non-zero)
    )))

(def-constant neg_1
  "-_mod(1)"
  (theory arithmetic-mod-n))

(def-theorem add-neg_1-typical-case
  "forall(x:zz_mod, not(x=0) implies +_mod(x,neg_1)=x-1)"
  (theory arithmetic-mod-n)
  (proof
   (


    (unfold-single-defined-constant (0) neg_1)
    (apply-macete-with-minor-premises -_mod-computation-non-zero)
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises +_mod-characterization)
    (move-to-sibling 1)
    (block 
      (script-comment "`apply-macete-with-minor-premises' at (1)")
      (apply-macete-with-minor-premises zz_mod-defining-axiom_arithmetic-mod-n)
      (cut-with-single-formula "#(x,zz_mod)")
      (incorporate-antecedent "with(x:zz_mod,#(x,zz_mod));")
      (apply-macete-with-minor-premises zz_mod-defining-axiom_arithmetic-mod-n)
      simplify)
    (block 
      (script-comment "`apply-macete-with-minor-premises' at (0)")
      direct-and-antecedent-inference-strategy
      (block 
	(script-comment "`direct-and-antecedent-inference-strategy' at (0)")
	(cut-with-single-formula "#(x,zz_mod)")
	(incorporate-antecedent "with(x:zz_mod,#(x,zz_mod));")
	(apply-macete-with-minor-premises zz_mod-defining-axiom_arithmetic-mod-n)
	simplify)
      (block 
	(script-comment "`direct-and-antecedent-inference-strategy' at (1)")
	(weaken (0))
	simplify
	(cut-with-single-formula "#(x,zz_mod)")
	(incorporate-antecedent "with(x:zz_mod,#(x,zz_mod));")
	(apply-macete-with-minor-premises zz_mod-defining-axiom_arithmetic-mod-n)
	simplify)
      (block 
	(script-comment "`direct-and-antecedent-inference-strategy' at (2)")
	(unfold-single-defined-constant (0) congruent)
	simplify
	(apply-macete-with-minor-premises multiplication-preserves-divisibility)
	(apply-macete-with-minor-premises self-divisibility)
	simplify))

    )))

(def-theorem add-neg_1-0
  "forall(x:zz_mod, +_mod(0,neg_1)=modulus-1)"
  (theory arithmetic-mod-n)
  (proof
   (


    (unfold-single-defined-constant (0) neg_1)
    (apply-macete-with-minor-premises -_mod-computation-non-zero)
    (apply-macete-with-minor-premises +_mod-characterization)
    (unfold-single-defined-constant (0) congruent)
    (unfold-single-defined-constant (0) divides)
    simplify

    )))
    
(def-theory arithmetic-mod-5
  (component-theories arithmetic-mod-n)
  (axioms
   (modular-value "modulus=5")))


(def-theorem example-op
  "+_mod(2,3)=0"
  (theory arithmetic-mod-5)
  (proof
   (



    (unfold-single-defined-constant (0) +_mod)
    (unfold-single-defined-constant (0) mod)
    (apply-macete-with-minor-premises modular-value)
    beta-reduce-with-minor-premises
    simplify
    (block 
      (script-comment "node added by `beta-reduce-with-minor-premises' at (1)")
      (apply-macete-with-minor-premises zz_mod-defining-axiom_arithmetic-mod-n)
      (apply-macete-with-minor-premises modular-value)
      simplify)
    (block 
      (script-comment "node added by `beta-reduce-with-minor-premises' at (2)")
      (apply-macete-with-minor-premises zz_mod-defining-axiom_arithmetic-mod-n)
      (apply-macete-with-minor-premises modular-value)
      simplify)

    )))


(def-script MOD-PLUS-COMPUTE 0
  
  (
   (unfold-single-defined-constant (0) +_mod)
   (unfold-single-defined-constant (0) mod)
   (apply-macete-with-minor-premises modular-value)
   beta-reduce-with-minor-premises
   simplify
   (block 
     (script-comment "node added by `beta-reduce-with-minor-premises' at (1)")
     (apply-macete-with-minor-premises zz_mod-defining-axiom_arithmetic-mod-n)
     (apply-macete-with-minor-premises modular-value)
     simplify)
   (block 
     (script-comment "node added by `beta-reduce-with-minor-premises' at (2)")
     (apply-macete-with-minor-premises zz_mod-defining-axiom_arithmetic-mod-n)
     (apply-macete-with-minor-premises modular-value)
     simplify)

   ))



(def-theorem example-op-1
  "+_mod(2,4)=1"
  (theory arithmetic-mod-5)
  (proof
   (
    mod-plus-compute
    )))


