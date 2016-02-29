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

(herald gcd)

;;(set (proof-log-port) (standard-output))

(include-files 
 (files (imps theories/machine-arithmetic/machine-arithmetic)))

(def-script set-equality-script 0
  (
   (label-node top)
   (apply-macete-with-minor-premises tr%subseteq-antisymmetry)
   direct-and-antecedent-inference-strategy
   (jump-to-node top)
   (for-nodes
    (unsupported-descendents)
    (block
      insistent-direct-inference
      (apply-macete-with-minor-premises indicator-facts-macete)
      beta-reduce-repeatedly))
   ))

(def-theorem gcd-for-zero
  "forall(a:zz, 0<=a implies gcd(a,0)=a)"
  (theory h-o-real-arithmetic)
  (proof
   (


    (unfold-single-defined-constant (0) gcd)
    simplify
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises iota-free-characterization-of-generator)
    direct-and-antecedent-inference-strategy
    set-equality-script
    (block
     (script-comment "`set-equality-script' at (0 0 0 0 0)")
     direct-and-antecedent-inference-strategy
     (unfold-single-defined-constant (0) princ%ideal)
     (case-split ("a=0"))
     (block
      (script-comment "`case-split' at (1)")
      simplify
      (simplify-antecedent "with(a,r,x_$2:zz,x_$2=r*a);"))
     (block
      (script-comment "`case-split' at (2)")
      simplify
      (apply-macete-with-minor-premises divisibility-lemma)
      auto-instantiate-existential))
    (block
     (script-comment "`set-equality-script' at (0 1 0 0 0)")
     (unfold-single-defined-constant (0) princ%ideal)
     (case-split ("a=0"))
     simplify
     (block
      (script-comment "`case-split' at (2)")
      simplify
      (apply-macete-with-minor-premises divisibility-lemma)))
    (unfold-single-defined-constant (0) princ%ideal)
    )))

(def-theorem gcd-of-negative
  "forall(u,v:zz, gcd(u,v)=gcd(-u,v))"
  (theory h-o-real-arithmetic)
  reverse
  (proof
   (


    unfold-defined-constants
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula
     "indic{x:zz,  forsome(r,s:zz,x=r*(-u)+s*v)}=
      indic{x:zz,  forsome(r,s:zz,x=r*u+s*v)}")
    (block 
      (script-comment "`cut-with-single-formula' at (0)")
      (backchain "with(p:prop,p);")
      simplify
      (apply-macete-with-minor-premises definedness-of-generator)
      (force-substitution "v*s+u*r" "r*u+s*v" (0))
      (move-to-sibling 1)
      simplify
      (apply-macete-with-minor-premises integer-combinations-form-an-ideal))
    (block 
      (script-comment "`cut-with-single-formula' at (1)")
      set-equality-script
      (block 
	(script-comment "`set-equality-script' at (0 0 0 0 0)")
	direct-and-antecedent-inference-strategy
	(instantiate-existential ("-r" "s"))
	(backchain "with(p:prop,p);")
	(weaken (0))
	simplify)
      (block 
	(script-comment "`set-equality-script' at (0 1 0 0 0)")
	direct-and-antecedent-inference-strategy
	(instantiate-existential ("-r" "s"))
	(backchain "with(r:rr,x_$1:zz,x_$1=r);")
	(weaken (0))
	simplify))

    )))

(def-theorem invariance-of-gcd-special-case
  "forall(u,v:zz, 0<v implies gcd(u,v)=gcd(mod(u,v),v))"
  (theory h-o-real-arithmetic)
  lemma
  (proof
   (


    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "forsome(z:zz, u mod v = z)")
    (block 
      (script-comment "`cut-with-single-formula' at (0)")
      (antecedent-inference "with(p:prop,forsome(z:zz,p));")
      (backchain "with(z:zz,r:rr,r=z);")
      (incorporate-antecedent "with(z:zz,r:rr,r=z);")
      (apply-macete-with-minor-premises mod-characterization)
      (apply-macete-with-minor-premises divisibility-lemma)
      direct-and-antecedent-inference-strategy
      (cut-with-single-formula "z=u-k*v")
      (move-to-sibling 1)
      simplify
      (block 
	(script-comment "`cut-with-single-formula' at (0)")
	(backchain "with(r:rr,u,z:zz,z=u-r);")
	(weaken (0 1 2 3))
	(unfold-single-defined-constant-globally gcd)
	(cut-with-single-formula "indic{x:zz,  forsome(r,s:zz,x=r*u+s*v)}=indic{x:zz,  forsome(r,s:zz,x=r*(u-k*v)+s*v)}")
	(block 
	  (script-comment "`cut-with-single-formula' at (0)")
	  (backchain-backwards "with(f:sets[zz],f=f);")
	  simplify
	  (apply-macete-with-minor-premises definedness-of-generator)
	  (force-substitution "v*s+u*r" "r*u+s*v" (0))
	  (move-to-sibling 1)
	  simplify
	  (apply-macete-with-minor-premises integer-combinations-form-an-ideal))
	(block 
	  (script-comment "`cut-with-single-formula' at (1)")
	  set-equality-script
	  (block 
	    (script-comment "`set-equality-script' at (0 0 0 0 0)")
	    direct-and-antecedent-inference-strategy
	    (backchain "with(r:rr,x_$2:zz,x_$2=r);")
	    (weaken (0))
	    (instantiate-existential ("r" "r*k+s"))
	    simplify)
	  (block 
	    (script-comment "`set-equality-script' at (0 1 0 0 0)")
	    direct-and-antecedent-inference-strategy
	    (backchain "with(r:rr,x_$1:zz,x_$1=r);")
	    (weaken (0 1))
	    (instantiate-existential ("r" "s-r*k"))
	    simplify))))
    (block 
      (script-comment "`cut-with-single-formula' at (1)")
      (instantiate-existential ("u mod v"))
      (block 
	(script-comment "`instantiate-existential' at (0)")
	simplify
	(unfold-single-defined-constant (0) mod)
	simplify)
      (apply-macete-with-minor-premises mod-of-integer-is-integer))

    )))


(def-theorem invariance-of-gcd
  "forall(u,v:zz, not(v=0) implies gcd(u,v)=gcd(mod(u,v),v))"
  (theory h-o-real-arithmetic)
  reverse
  (proof
   (


    direct-and-antecedent-inference-strategy
    (case-split ("0<v"))
    (instantiate-theorem invariance-of-gcd-special-case ("u" "v"))
    (block
     (script-comment "`case-split' at (2)")
     (force-substitution "gcd(u mod v,v)" "gcd((-u) mod (-v),-v)" (0))
     (move-to-sibling 1)
     (block
      (script-comment "`force-substitution' at (1)")
      (apply-macete-with-minor-premises mod-of-negative)
      (apply-macete-with-minor-premises rev%gcd-of-negative)
      (apply-macete-with-minor-premises symmetry-of-gcd)
      (apply-macete-with-minor-premises rev%gcd-of-negative)
      (apply-macete-with-minor-premises mod-of-integer-is-integer)
      direct-and-antecedent-inference-strategy)
     (block
      (script-comment "`force-substitution' at (0)")
      (instantiate-theorem invariance-of-gcd-special-case ("-u" "-v"))
      (simplify-antecedent "with(v:zz,not(0<-v));")
      (block
       (script-comment "`instantiate-theorem' at (0 1)")
       (backchain-backwards "with(z:zz,z=z);")
       (apply-macete-with-minor-premises rev%gcd-of-negative)
       (apply-macete-with-minor-premises symmetry-of-gcd)
       (apply-macete-with-minor-premises rev%gcd-of-negative)
       simplify
       (unfold-single-defined-constant (0) gcd)
       (apply-macete-with-minor-premises definedness-of-generator)
       (apply-macete-with-minor-premises integer-combinations-form-an-ideal))))

    )))

(def-theorem gcd-of-multiple
  "forall(a,m:zz, 0<m and m divides a implies gcd(a,m)=m)"
  (theory h-o-real-arithmetic)
  (proof
   (


    (unfold-single-defined-constant (0) gcd)
    (apply-macete-with-minor-premises iota-free-characterization-of-generator)
    (unfold-single-defined-constant (0) princ%ideal)
    simplify
    (apply-macete-with-minor-premises divisibility-lemma)
    (block
     (script-comment "`apply-macete-with-minor-premises' at (0)")
     direct-and-antecedent-inference-strategy
     (backchain "with(r:rr,a:zz,a=r);")
     (weaken (0))
     set-equality-script
     (block
      (script-comment "`set-equality-script' at (0 0 0 0 0)")
      direct-and-antecedent-inference-strategy
      (backchain "with(r:rr,x:zz,x=r);")
      (weaken (0))
      (instantiate-existential ("r*k+s"))
      simplify)
     (block
      (script-comment "`set-equality-script' at (0 1 0 0 0)")
      direct-and-antecedent-inference-strategy
      (backchain "with(r:rr,x_$0:zz,x_$0=r);")
      (weaken (0))
      (instantiate-existential ("1" "(-k+k_$0)"))
      simplify))
    )))

(def-theorem gcd-is-gcd-of-absolute-value
  "forall(u,v:zz, gcd(u,v)=gcd(abs(u),abs(v)))"
  (theory h-o-real-arithmetic)
  (proof
   (


    direct-and-antecedent-inference-strategy
    (case-split ("0<=u" "0<=v"))
    (block
     (script-comment "`case-split' at (1)")
     (apply-macete-with-minor-premises absolute-value-non-negative)
     simplify
     (unfold-single-defined-constant (0) gcd)
     (apply-macete-with-minor-premises definedness-of-generator)
     (apply-macete-with-minor-premises integer-combinations-form-an-ideal))
    (block
     (script-comment "`case-split' at (2)")
     (apply-macete absolute-value-non-positive)
     (apply-macete-with-minor-premises absolute-value-non-negative)
     (apply-macete-with-minor-premises symmetry-of-gcd)
     (apply-macete-with-minor-premises rev%gcd-of-negative)
     simplify
     (unfold-single-defined-constant (0) gcd)
     (apply-macete-with-minor-premises definedness-of-generator)
     (apply-macete-with-minor-premises integer-combinations-form-an-ideal))
    (block
     (script-comment "`case-split' at (3)")
     (apply-macete absolute-value-non-positive)
     (apply-macete-with-minor-premises absolute-value-non-negative)
     (apply-macete-with-minor-premises rev%gcd-of-negative)
     simplify
     (unfold-single-defined-constant (0) gcd)
     (apply-macete-with-minor-premises definedness-of-generator)
     (apply-macete-with-minor-premises integer-combinations-form-an-ideal))
    (block
     (script-comment "`case-split' at (4)")
     (apply-macete-with-minor-premises absolute-value-non-positive)
     (apply-macete-with-minor-premises rev%gcd-of-negative)
     (apply-macete-with-minor-premises symmetry-of-gcd)
     (apply-macete-with-minor-premises rev%gcd-of-negative)
     simplify
     (unfold-single-defined-constant (0) gcd)
     (apply-macete-with-minor-premises definedness-of-generator)
     (apply-macete-with-minor-premises integer-combinations-form-an-ideal))
    )))

(def-recursive-constant gcd_rho
  "lambda(f:[zz,zz->zz], 
        lambda(u,v:zz, if(0<=v and 0<=u,if(u=0, v,v=0,u,f(v,mod(u,v))), ?zz)))"
  (definition-name gcd_rho)
  (theory h-o-real-arithmetic))


(def-theorem gcd_rho-defined-for-nonnegative-args
  "forall(a,b:zz, 0<=a and 0<=b implies #(gcd_rho(a,b)))"
  (theory h-o-real-arithmetic)
  (proof
   (


    (cut-with-single-formula
     "forall(b:zz, 0<=b implies forall(a:zz, 0<=a implies 
#(gcd_rho(a,b))))")
    (block
     (script-comment "`cut-with-single-formula' at (0)")
     direct-and-antecedent-inference-strategy
     (backchain "with(p:prop,forall(b:zz,p));")
     direct-and-antecedent-inference-strategy)
    (block
     (script-comment "`cut-with-single-formula' at (1)")
     (induction complete-inductor ("b"))
     (case-split ("a=0"))
     simplify
     (block
      (script-comment "`case-split' at (2)")
      simplify
      (case-split ("m=0"))
      simplify
      (block
       (script-comment "`case-split' at (2)")
       simplify
       beta-reduce-with-minor-premises
       (move-to-sibling 1)
       (apply-macete-with-minor-premises mod-of-integer-is-integer)
       (block
	(script-comment "`beta-reduce-with-minor-premises' at (0)")
	(instantiate-theorem division-with-remainder
			     ("m" "a"))
	(simplify-antecedent "with(m:zz,not(0<m));")
	(block
	 (script-comment "`instantiate-theorem' at (0 1 0)")
	 simplify
	 (case-split ("a mod m = 0"))
	 simplify
	 (block
	  (script-comment "`case-split' at (2)")
	  simplify
	  (backchain "with(p:prop,forall(k:zz,p));")
	  (block
	   (script-comment "`backchain' at (0)")
	   (instantiate-theorem division-with-remainder
                                                                 
				("a mod m" "m"))
	   (simplify-antecedent "with(r:rr,not(0<r));")
	   (block
	    (script-comment "`instantiate-theorem' at (0 1 0)")
	    direct-and-antecedent-inference-strategy
	    simplify))
	  (apply-macete-with-minor-premises mod-of-integer-is-integer)))))))


    )))

(def-theorem gcd_rho-is-gcd
  "forall(x,y:zz, 0<=x and 0<=y implies gcd_rho(x,y)=gcd(x,y))"
  (theory h-o-real-arithmetic)
  (proof
   (


    direct-and-antecedent-inference-strategy
    (instantiate-theorem gcd_rho-strong-minimality_h-o-real-arithmetic ("gcd"))
    (block
     (script-comment "`instantiate-theorem' at (0 0 0 0)")
     (contrapose "with(p:prop,not(p));")
     (case-split ("0<=u_1 and 0<=u_0"))
     simplify
     (case-split ("u_0=0"))
     (block
      (script-comment "`case-split' at (1)")
      simplify
      (apply-macete-with-minor-premises symmetry-of-gcd)
      (apply-macete-with-minor-premises gcd-for-zero))
     (block
      (script-comment "`case-split' at (2)")
      simplify
      (case-split ("u_1=0"))
      (block
       (script-comment "`case-split' at (1)")
       simplify
       (apply-macete-with-minor-premises gcd-for-zero))
      (block
       (script-comment "`case-split' at (2)")
       simplify
       (apply-macete-with-minor-premises symmetry-of-gcd)
       (apply-macete-with-minor-premises rev%invariance-of-gcd)
       (apply-macete-locally symmetry-of-gcd (0) "gcd(u_0,u_1)")
       simplify
       (unfold-single-defined-constant (0) gcd)
       (apply-macete-with-minor-premises definedness-of-generator)
       (apply-macete-with-minor-premises integer-combinations-form-an-ideal))))
    (block
     (script-comment "`instantiate-theorem' at (0 1)")
     (backchain "with(p:prop,forall(u_0,u_1:zz,p));")
     (apply-macete-with-minor-premises gcd_rho-defined-for-nonnegative-args)
     direct-and-antecedent-inference-strategy)

    )))


(def-recursive-constant gcd_ma
  "lambda(f:[int,int->int], 
        lambda(u,v:int, if(0<=v and 0<=u,if(u=0, v,v=0,u,f(v,mod_ma(u,v))), abs_ma(0))))"
  (definition-name gcd_ma)
  (theory machine-arithmetic))

(def-theorem gcd_ma-restricts-gcd
  "forall(a,b:int, 0<=a and 0<=b implies gcd_ma(a,b)=gcd(a,b))"
  (theory machine-arithmetic)
  (proof

   (

    
    (cut-with-single-formula
     "forall(b:zz, 0<=b and b<=maxint 
                    implies 
                   forall(a:zz, 0<=a and a<=maxint implies gcd_ma(a,b)=gcd(a,b)))")
    (block
     (script-comment "`cut-with-single-formula' at (0)")
     direct-and-antecedent-inference-strategy
     (backchain "with(p:prop,forall(b:zz,p));")
     direct-and-antecedent-inference-strategy
     (block
      (script-comment "`direct-and-antecedent-inference-strategy' at (0 1)")
      (cut-with-single-formula "#(b,int)")
      (incorporate-antecedent "with(b:int,#(b,int));")
      (apply-macete-with-minor-premises int-defining-axiom_machine-arithmetic)
      beta-reduce-repeatedly
      direct-and-antecedent-inference-strategy)
     (block
      (script-comment "`direct-and-antecedent-inference-strategy' at (1 1 0)")
      (cut-with-single-formula "#(a,int)")
      (incorporate-antecedent "with(a:int,#(a,int));")
      (apply-macete-with-minor-premises int-defining-axiom_machine-arithmetic)
      beta-reduce-repeatedly
      direct-and-antecedent-inference-strategy))
    (block
     (script-comment "`cut-with-single-formula' at (1)")
     (induction complete-inductor ("b"))
     (case-split ("a=0"))
     (block
      (script-comment "`case-split' at (1)")
      simplify
      (apply-macete-with-minor-premises symmetry-of-gcd)
      (apply-macete-with-minor-premises gcd-for-zero))
     (block
      (script-comment "`case-split' at (2)")
      simplify
      (case-split ("m=0"))
      (block
       (script-comment "`case-split' at (1)")
       simplify
       (apply-macete-with-minor-premises gcd-for-zero))
      (block
       (script-comment "`case-split' at (2)")
       simplify
       beta-reduce-with-minor-premises
       (move-to-sibling 1)
       (block
	(script-comment "`beta-reduce-with-minor-premises' at (1)")
	(unfold-single-defined-constant (0) mod_ma)
	(cut-with-single-formula "#(a mod m ,zz)")
	(apply-macete-with-minor-premises mod-of-integer-is-integer))
       (block
	(script-comment "`beta-reduce-with-minor-premises' at (0)")
	(unfold-single-defined-constant-globally mod_ma)
	(instantiate-theorem division-with-remainder
			     ("m" "a"))
	(simplify-antecedent "with(m:zz,not(0<m));")
	(block
	 (script-comment "`instantiate-theorem' at (0 1 0)")
	 simplify
	 (case-split ("a mod m = 0"))
	 (block
	  (script-comment "`case-split' at (1)")
	  simplify
	  (contrapose "with(r:rr,r=0);")
	  (apply-macete-with-minor-premises mod-characterization)
	  simplify
	  (contrapose "with(a,m:zz,not(m=gcd(a,m)));")
	  (apply-macete-with-minor-premises gcd-of-multiple))
	 (block
	  (script-comment "`case-split' at (2)")
	  simplify
	  (backchain "with(p:prop,forall(k:zz,p));")
	  (move-to-sibling 1)
	  (apply-macete-with-minor-premises mod-of-integer-is-integer)
	  (block
	   (script-comment "`backchain' at (0)")
	   (instantiate-theorem division-with-remainder
                                                                 
				("a mod m" "m"))
	   (simplify-antecedent "with(r:rr,not(0<r));")
	   (block
	    (script-comment "`instantiate-theorem' at (0 1 0)")
	    direct-and-antecedent-inference-strategy
	    simplify
	    simplify
	    (block
	     (script-comment
	      "`direct-and-antecedent-inference-strategy' at (1 1 1 0 0)")
	     (apply-macete-with-minor-premises symmetry-of-gcd)
	     (block
	      (script-comment "`apply-macete-with-minor-premises' at (0)")
	      (apply-macete-with-minor-premises rev%invariance-of-gcd)
	      (apply-macete-with-minor-premises symmetry-of-gcd)
	      (apply-macete-with-minor-premises rev%invariance-of-gcd)
	      simplify
	      (unfold-single-defined-constant (0) gcd)
	      (apply-macete-with-minor-premises definedness-of-generator)
	      (apply-macete-with-minor-premises 
	       integer-combinations-form-an-ideal))
	     (apply-macete-with-minor-premises mod-of-integer-is-integer))))))))))
    )


   ))
