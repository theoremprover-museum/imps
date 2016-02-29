;;% Copyright (c) 1990-1994 The MITRE Corporation
;;% 
;;% Authors: W. M. Farmer, J. D. Guttman, F. J. Thayer
;;%   
;;% The MITRE Corporation (MITRE) provides this software to you without
;;% charge to use, copy, modify or enhance for any legitimate purpose
;;% provided you reproduce MITRE's copyright notice in any copy or
;;% derivative work of this software.
;;% 
;;% This software is the copyright work of MITRE.  No ownership or other
;;% proprietary interest in this software is granted you other than what
;;% is granted in this license.
;;% 
;;% Any modification or enhancement of this software must identify the
;;% part of this software that was modified, by whom and when, and must
;;% inherit this license including its warranty disclaimers.
;;% 
;;% MITRE IS PROVIDING THE PRODUCT "AS IS" AND MAKES NO WARRANTY, EXPRESS
;;% OR IMPLIED, AS TO THE ACCURACY, CAPABILITY, EFFICIENCY OR FUNCTIONING
;;% OF THIS SOFTWARE AND DOCUMENTATION.  IN NO EVENT WILL MITRE BE LIABLE
;;% FOR ANY GENERAL, CONSEQUENTIAL, INDIRECT, INCIDENTAL, EXEMPLARY OR
;;% SPECIAL DAMAGES, EVEN IF MITRE HAS BEEN ADVISED OF THE POSSIBILITY OF
;;% SUCH DAMAGES.
;;% 
;;% You, at your expense, hereby indemnify and hold harmless MITRE, its
;;% Board of Trustees, officers, agents and employees, from any and all
;;% liability or damages to third parties, including attorneys' fees,
;;% court costs, and other related costs and expenses, arising out of your
;;% use of this software irrespective of the cause of said liability.
;;% 
;;% The export from the United States or the subsequent reexport of this
;;% software is subject to compliance with United States export control
;;% and munitions control restrictions.  You agree that in the event you
;;% seek to export this software or any derivative work thereof, you
;;% assume full responsibility for obtaining all necessary export licenses
;;% and approvals and for assuring compliance with applicable reexport
;;% restrictions.
;;% 
;;% 
;;% COPYRIGHT NOTICE INSERTED: Mon Apr 11 11:42:27 EDT 1994

(herald machine-arithmetic)

;; (set (proof-log-port) (standard-output))

(load-section number-theory)

(include-files
 (files (imps /theories/machine-arithmetic/ma-presentation)))


;;; Machine arithmetic theory

(def-language mach-arith-language
  (embedded-language h-o-real-arithmetic)
  (constants (maxint zz)
	     (minint zz)))

(def-theory machine-arithmetic
  (language mach-arith-language)
  (component-theories h-o-real-arithmetic)
  (axioms
   (maxint-is-positive "0 < maxint")
   (minint-is-negative-maxint "minint = -maxint")))

(def-theorem minint-is-negative
  "minint < 0"
  (theory machine-arithmetic)
  (proof
   (

    (apply-macete-with-minor-premises minint-is-negative-maxint)
    simplify

    )))

;;; Atomic sort int

(def-atomic-sort int
  "lambda(i:zz, minint <= i and i <= maxint)"
  (theory machine-arithmetic)
  (witness "0"))

;;; Predicate constants

(def-constant =_ma
  "lambda(x,y:int, x=y)"
  (theory machine-arithmetic))

(def-constant <_ma
  "lambda(x,y:int, x<y)"
  (theory machine-arithmetic))

(def-constant <=_ma
  "lambda(x,y:int, x<=y)"
  (theory machine-arithmetic))

(def-constant >_ma
  "lambda(x,y:int, x>y)"
  (theory machine-arithmetic))

(def-constant >=_ma
  "lambda(x,y:int, x>=y)"
  (theory machine-arithmetic))

;;; Constants with overflow

(def-script closed-on-int-2 0
  (
   sort-definedness
   direct-inference
   (case-split ("#(xx_0,int) and #(xx_1,int)"))
   simplify
   (simplify-antecedent "with(p:prop,p);")
   ))

(def-script unfold-ma-defined-expression 1
  (
   direct-inference
   (unfold-single-defined-constant-globally $1)
   (case-split ("#(x,int) and #(y,int)"))
   simplify
   (simplify-antecedent "with(p:prop,p);")
   ))

(def-theorem ()
  "#(lambda(x,y:int,if(#(x+y,int), x+y, ?int)),[int,int,int])"
  lemma
  (theory machine-arithmetic)
  (proof 
   (

    closed-on-int-2

    )))

(def-constant +_ma
  "lambda(x,y:int, if(#(x+y,int),x+y,?int))"
  (sort "[int,int,int]")
  (theory machine-arithmetic))

(def-theorem unfold-defined-expression%+_ma
  "forall(x,y:zz, #(x +_ma y) implies x +_ma y = x + y)"
  (theory machine-arithmetic)
  (proof
   (

    (unfold-ma-defined-expression +_ma)

    )))

(def-theorem ()
  "#(lambda(x,y:int,if(#(x*y,int), x*y, ?int)),[int,int,int])"
  lemma
  (theory machine-arithmetic)
  (proof
   (

    closed-on-int-2

    )))

(def-constant *_ma
  "lambda(x,y:int, if(#(x*y,int),x*y,?int))"
  (sort "[int,int,int]")
  (theory machine-arithmetic))

(def-theorem unfold-defined-expression%*_ma
  "forall(x,y:zz, #(x *_ma y) implies x *_ma y = x * y)"
  (theory machine-arithmetic)
  (proof
   (

    (unfold-ma-defined-expression *_ma)

    )))

(def-theorem ()
  "#(lambda(x,y:int,if(#(x-y,int), x-y, ?int)),[int,int,int])"
  lemma
  (theory machine-arithmetic)
  (proof
   (

    closed-on-int-2

    )))

(def-constant sub_ma
  "lambda(x,y:int,if(#(x-y,int), x-y, ?int))"
  (sort "[int,int,int]")
  (theory machine-arithmetic))

(def-theorem unfold-defined-expression%sub_ma
  "forall(x,y:zz, #(x sub_ma y) implies x sub_ma y = x - y)"
  (theory machine-arithmetic)
  (proof
   (

    (unfold-ma-defined-expression sub_ma)

    )))

;;;; Other constants

(def-theorem unary-int-function-lemma
  "forall(f:[rr,rr], 
     forall(x:zz, 
       abs(f(x)) <= abs(x) and (#(f(x)) implies #(f(x),zz)))
      implies 
     #(lambda(x:int, f(x)),[int,int]))"
  lemma
  (theory machine-arithmetic)
  (proof
   (

    direct-and-antecedent-inference-strategy
    sort-definedness
    direct-inference
    (case-split ("#(xx_0,int)"))
    (block 
     (script-comment "node added by `case-split' at (1)")
     simplify
     (cut-with-single-formula "#(xx_0,int) and 0=0")
     (incorporate-antecedent "with(xx_0:ind,#(xx_0,int));")
     (apply-macete-with-minor-premises int-defining-axiom_machine-arithmetic)
     (apply-macete-with-minor-premises minint-is-negative-maxint)
     (instantiate-universal-antecedent "with(p:prop,forall(x:zz,p));" ("xx_0"))
     (incorporate-antecedent "with(r:rr,r<=r);")
     (unfold-single-defined-constant-globally abs)
     (case-split-on-conditionals (1))
     (case-split-on-conditionals (0))
     (case-split-on-conditionals (0)))
    simplify

    )))

(def-theorem binary-int-function-lemma
  "forall(f:[rr,rr,rr], 
     forall(x,y:zz, 
       abs(f(x,y)) <= abs(x) and (#(f(x,y)) implies #(f(x,y),zz)))
      implies 
     #(lambda(x,y:int, f(x,y)),[int,int,int]))"
  lemma
  (theory machine-arithmetic)
  (proof
   (

    direct-and-antecedent-inference-strategy
    sort-definedness
    direct-inference
    (case-split ("#(xx_0,int) and #(xx_1,int)"))
    (block 
     (script-comment "node added by `case-split' at (1)")
     simplify
     (cut-with-single-formula "#(xx_0,int) and #(xx_1,int) and 0=0")
     (incorporate-antecedent "with(p:prop,p and p);")
     (apply-macete-with-minor-premises int-defining-axiom_machine-arithmetic)
     (apply-macete-with-minor-premises minint-is-negative-maxint)
     (instantiate-universal-antecedent "with(p:prop,forall(x,y:zz,p));"
				       ("xx_0" "xx_1"))
     (incorporate-antecedent "with(r:rr,r<=r);")
     (unfold-single-defined-constant-globally abs)
     (case-split-on-conditionals (1))
     (case-split-on-conditionals (0))
     (case-split-on-conditionals (0)))
    (block 
     (script-comment "node added by `case-split' at (2)")
     simplify
     (simplify-antecedent "with(p:prop,not(p));"))  

    )))

(def-theorem int-minus-lemma
  "forall(x:int, #(-x,int))"
  (theory machine-arithmetic)
  (proof
   (
    
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "#(x,int)")
    (incorporate-antecedent "with(p:prop,p);")
    (apply-macete-with-minor-premises int-defining-axiom_machine-arithmetic)
    (apply-macete-with-minor-premises minint-is-negative-maxint)
    simplify

    )))

(def-theorem ()
  "#(lambda(x:int, -x),[int,int])"
  lemma
  (theory machine-arithmetic)
  (proof
   (

    (apply-macete-with-minor-premises unary-int-function-lemma)
    simplify
    (unfold-single-defined-constant-globally abs)
    (raise-conditional (0))
    (raise-conditional (0))
    (raise-conditional (0))
    simplify

    )))

(def-constant -_ma
  "lambda(x:int, -x)"
  (sort "[int,int]")
  (theory machine-arithmetic))

(def-theorem ()
  "#(lambda(x:int, abs(x)),[int,int])"
  lemma
  (theory machine-arithmetic)
  (proof
   (

    (apply-macete-with-minor-premises unary-int-function-lemma)
    simplify
    (unfold-single-defined-constant-globally abs)
    simplify

    )))

(def-constant abs_ma
  "lambda(x:int, abs(x))"
  (sort "[int,int]")
  (theory machine-arithmetic))

(def-theorem maxint-division-lemma
  "forall(a:int,b:zz, not(b=0) implies a/b<=maxint)"
  (theory  machine-arithmetic)
  (proof
   (

    (cut-with-single-formula "forall(a:int,b:zz,0<b implies a/b<=maxint)")
    (block
     (script-comment "`cut-with-single-formula' at (0)")
     direct-and-antecedent-inference-strategy
     (case-split ("0<b"))
     simplify
     (block
      (script-comment "`case-split' at (2)")
      (force-substitution "a/b" "(-a)/(-b)" (0))
      (block
       (script-comment "`force-substitution' at (0)")
       (backchain "with(p:prop,forall(a:int,b:zz,p));")
       simplify
       (block
	(script-comment "`backchain' at (1)")
	(cut-with-single-formula "#(a,int)")
	(incorporate-antecedent "with(a:int,#(a,int));")
	(apply-macete-with-minor-premises 
	 int-defining-axiom_machine-arithmetic)
	(apply-macete-with-minor-premises minint-is-negative-maxint)
	simplify))
      simplify))
    (block
     (script-comment "`cut-with-single-formula' at (1)")
     direct-and-antecedent-inference-strategy
     (apply-macete-with-minor-premises fractional-expression-manipulation)
     (cut-with-single-formula "maxint<=maxint*b")
     (move-to-sibling 1)
     (block
      (script-comment "`cut-with-single-formula' at (1)")
      (cut-with-single-formula "0<=maxint*(b-1)")
      simplify
      simplify)
     (block
      (script-comment "`cut-with-single-formula' at (0)")
      (cut-with-single-formula "a<=maxint")
      simplify
      (block
       (script-comment "`cut-with-single-formula' at (1)")
       (cut-with-single-formula "minint <= a and a <= maxint")
       (apply-macete-with-minor-premises 
	int-in-quasi-sort_machine-arithmetic))))

    )))

(def-theorem minint-division-lemma
  "forall(a:int,b:zz, not(b=0) implies minint<=a/b)"
  (theory  machine-arithmetic)
  (proof
   (

    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises minint-is-negative-maxint)
    (cut-with-single-formula "(-a)/b<=maxint")
    simplify
    (block
     (script-comment "node added by `cut-with-single-formula' at (1)")
     (apply-macete-with-minor-premises maxint-division-lemma)
     (cut-with-single-formula "#(a,int)")
     (incorporate-antecedent "with(a:int,#(a,int));")
     (apply-macete-with-minor-premises int-defining-axiom_machine-arithmetic)
     (apply-macete-with-minor-premises minint-is-negative-maxint)
     simplify)

    )))

(def-theorem int-division-lemma
  "forall(a:int,b:zz, not(b=0) implies #(a div b,int))"
  (theory  machine-arithmetic)
  (proof
   (
    	
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises int-defining-axiom_machine-arithmetic)
    beta-reduce-repeatedly
    (unfold-single-defined-constant-globally div)
    (apply-macete-with-minor-premises floor-not-much-below-arg)
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises minint-division-lemma)
    (block
     (script-comment "`direct-and-antecedent-inference-strategy' at (1)")
     (cut-with-single-formula "floor(a/b)<=a/b and a/b<=maxint")
     simplify
     (block
      (script-comment "`cut-with-single-formula' at (1)")
      (apply-macete-with-minor-premises floor-below-arg)
      (apply-macete-with-minor-premises maxint-division-lemma)))

    )))

(def-theorem ()
  "#(lambda(x,y:int, x div y),[int,int,int])"
  lemma
  (theory machine-arithmetic)
  (proof
   (
    
    sort-definedness
    direct-inference
    (case-split ("#(xx_0,int) and #(xx_1,int) and not xx_1 =0 "))
    (block
     (script-comment "`case-split' at (1)")
     beta-reduce-repeatedly
     (apply-macete-with-minor-premises int-division-lemma)
     direct-and-antecedent-inference-strategy)
    (block
     (script-comment "`case-split' at (2)")
     beta-reduce-repeatedly
     (contrapose "with(p:prop,p);")
     direct-and-antecedent-inference-strategy
     (antecedent-inference "with(p:prop,p and p);")
     (contrapose "with(z:zz,#(z));")
     beta-reduce-repeatedly
     (unfold-single-defined-constant (0) div)
     simplify)

    )))

(def-constant div_ma
  "lambda(x,y:int, x div y)"
  (sort "[int,int,int]")
  (theory machine-arithmetic))

(def-theorem maxint-pos-mod-lemma
  "forall(a:zz,b:int, 0< b implies a mod b < maxint)"
  (theory  machine-arithmetic)
  (proof
   (

    direct-and-antecedent-inference-strategy
    (cut-with-single-formula " a mod b < b and b<=maxint")
    simplify
    (block
     (script-comment "`cut-with-single-formula' at (1)")
     (cut-with-single-formula "#(b,int)")
     (incorporate-antecedent "with(b:int,#(b,int));")
     (apply-macete-with-minor-premises int-defining-axiom_machine-arithmetic)
     beta-reduce-repeatedly
     direct-and-antecedent-inference-strategy
     (instantiate-theorem division-with-remainder ("b" "a")))

    )))

(def-theorem minint-pos-mod-lemma
  "forall(a:zz, b:int, 0< b implies minint < a mod b )"
  (theory  machine-arithmetic)
  (proof
   (

    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "0<= a mod b")
    simplify
    (instantiate-theorem division-with-remainder ("b" "a"))

    )))

(def-theorem int-mod-lemma
  "forall(a:zz, b:int, not(b=0) implies #(a mod b,int))"
  (theory machine-arithmetic)
  (proof
   (
    
    (cut-with-single-formula "forall(a:zz,b:int,0<b implies #(a mod b,int))")
    (block
     (script-comment "`cut-with-single-formula' at (0)")
     direct-and-antecedent-inference-strategy
     (case-split ("0<b"))
     simplify
     (block
      (script-comment "`case-split' at (2)")
      (force-substitution "a mod b" "-(- a mod -b)" (0))
      (block
       (script-comment "`force-substitution' at (0)")
       (apply-macete-with-minor-premises int-minus-lemma)
       (backchain "with(p:prop,forall(a:zz,b:int,p));")
       simplify
       (block
	(script-comment "`backchain' at (1)")
	(cut-with-single-formula "#(-b, int)")
	(simplify-antecedent "with(r:rr,#(r,int));")
	(apply-macete-with-minor-premises int-minus-lemma)))
      (block
       (script-comment "`force-substitution' at (1)")
       (apply-macete-with-minor-premises mod-of-negative)
       simplify)))
    (block
     (script-comment "`cut-with-single-formula' at (1)")
     direct-and-antecedent-inference-strategy
     (cut-with-single-formula "#(a mod b ,zz)")
     (block
      (script-comment "`cut-with-single-formula' at (0)")
      (apply-macete-with-minor-premises int-defining-axiom_machine-arithmetic)
      beta-reduce-repeatedly
      simplify
      (cut-with-single-formula "minint<a mod b and a mod b<maxint")
      simplify
      (block
       (script-comment "`cut-with-single-formula' at (1)")
       (apply-macete-with-minor-premises minint-pos-mod-lemma)
       (apply-macete-with-minor-premises maxint-pos-mod-lemma)))
     (block
      (script-comment "`cut-with-single-formula' at (1)")
      (apply-macete-with-minor-premises mod-of-integer-is-integer)
      simplify))

    )))

(def-theorem ()
  "#(lambda(x,y:int, x mod y),[int,int,int])"
  lemma
  (theory machine-arithmetic)
  (proof
   (

    sort-definedness
    direct-inference
    (case-split ("#(xx_0,int) and #(xx_1,int) and not xx_1 =0 "))
    (block 
     (script-comment "node added by `case-split' at (1)")
     beta-reduce-repeatedly
     (apply-macete-with-minor-premises int-mod-lemma)
     direct-and-antecedent-inference-strategy)
    (block 
     (script-comment "node added by `case-split' at (2)")
     beta-reduce-repeatedly
     (contrapose "with(p:prop,p);")
     direct-and-antecedent-inference-strategy
     (antecedent-inference "with(p:prop,p and p);")
     (contrapose "with(r:rr,#(r));")
     beta-reduce-repeatedly
     (unfold-single-defined-constant (0) mod)
     simplify)

    )))

(def-constant mod_ma
  "lambda(x,y:int, x mod y)"
  (sort "[int,int,int]")
  (theory machine-arithmetic))




