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


(herald monoids-supplements)

(include-files
 (files (imps theories/algebra/monoids)))

(def-theory monoids-with-index-set
  (component-theories commutative-monoid-theory generic-theory-1))

(def-constant monoid%prod%unordered
  "lambda(s:sets[ind_1], f:[ind_1,uu],
     iota(a:uu, forsome(m,n:zz,phi:[zz,ind_1], injective_q{phi} 
                           and 
                          zz%interval(m,n) subseteq dom{phi}
                           and
                          image{phi,zz%interval(m,n)} = s
                           and
                          a=monoid%prod(m,n,f oo phi))))"
  (theory monoids-with-index-set))

(def-theorem general-commutative-law-corollary-1
  "forall(a,b,c,d:zz, phi:[zz,zz], f:[zz,uu],
         zz%interval(c,d) subseteq dom{phi} and
         injective_q{phi} and 
         image{phi,zz%interval(c,d)}=zz%interval(a,b)
    implies
     monoid%prod(c,d,f oo phi) == monoid%prod(a,b,f))"
  lemma
  (theory commutative-monoid-theory)
  (usages transportable-macete)
  (proof
   (

    direct-and-antecedent-inference-strategy
    (case-split ("c<=d"))
    (apply-macete-with-minor-premises general-commutative-law-corollary)
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "not(a<=b)")
    unfold-defined-constants
    simplify
    (contrapose "with(d,c:zz,not(c<=d));")
    (incorporate-antecedent "with(b,a:zz,phi:[zz,zz],d,c:zz,
  image{phi,zz%interval(c,d)}=zz%interval(a,b));")
    (apply-macete-with-minor-premises tr%subseteq-antisymmetry)
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "a in zz%interval(a,b)")
    (cut-with-single-formula "a in image{phi,zz%interval(c,d)}")
    (incorporate-antecedent "with(a:zz,phi:[zz,zz],d,c:zz,
  a in image{phi,zz%interval(c,d)});")
    (apply-macete-with-minor-premises indicator-facts-macete)
    beta-reduce-repeatedly
    (unfold-single-defined-constant (0) zz%interval)
    (apply-macete-with-minor-premises indicator-facts-macete)
    beta-reduce-repeatedly
    direct-and-antecedent-inference-strategy
    simplify
    (backchain "with(phi:[zz,zz],d,c,b,a:zz,
  zz%interval(a,b) subseteq image{phi,zz%interval(c,d)});")
    (unfold-single-defined-constant (0) zz%interval)
    (apply-macete-with-minor-premises indicator-facts-macete)
    beta-reduce-repeatedly
    simplify
    (unfold-single-defined-constant (0) zz%interval)

    )))

(def-theorem general-commutative-law-corollary-2
  "forall(a,b,c,d:zz, phi:[zz,ind_1], psi:[zz,ind_1], f:[ind_1,uu],s:sets[ind_1],
         zz%interval(c,d) = dom{phi} and
         injective_q{phi} and 
         image{phi,zz%interval(c,d)}=s and
         zz%interval(a,b) = dom{psi} and
         injective_q{psi} and 
         image{psi,zz%interval(a,b)}=s
    implies
     monoid%prod(c,d,f oo phi) == monoid%prod(a,b,f oo psi))"
  lemma
  (theory monoids-with-index-set)
  (usages transportable-macete)
  (proof
   (


    direct-and-antecedent-inference-strategy
    (force-substitution "f oo phi" "(f oo psi) oo (inverse{psi}  oo phi)" (0))
    (block 
	(script-comment "`force-substitution' at (0)")
      (apply-macete-with-minor-premises general-commutative-law-corollary-1)
      direct-and-antecedent-inference-strategy
      (block 
	  (script-comment "`direct-and-antecedent-inference-strategy' at (0)")
	(backchain "with(phi:[zz,ind_1],d,c:zz,zz%interval(c,d)=dom{phi});")
	(apply-macete-with-minor-premises tr%domain-composition)
	(cut-with-single-formula "ran{phi}=ran{psi}")
	(block 
	    (script-comment "`cut-with-single-formula' at (0)")
	  (backchain "with(psi,phi:[zz,ind_1],ran{phi}=ran{psi});")
	  (apply-macete-with-minor-premises tr%inverse-defined-within-range)
	  )
	(block 
	    (script-comment "`cut-with-single-formula' at (1)") (weaken (0 2 5))
	    (cut-with-single-formula
	     "forall(psi:[zz,ind_1],image{psi,dom{psi}}=ran{psi})"
	     )
	    (block 
		(script-comment "`cut-with-single-formula' at (0)")
	      (backchain-backwards "with(p:prop,forall(psi:[zz,ind_1],p));")
	      (backchain-backwards "with(p:prop,forall(psi:[zz,ind_1],p));")
	      (backchain-backwards
	       "with(phi:[zz,ind_1],d,c:zz,zz%interval(c,d)=dom{phi});"
	       )
	      (backchain-backwards
	       "with(psi:[zz,ind_1],b,a:zz,zz%interval(a,b)=dom{psi});"
	       )
	      simplify
	      )
	    (apply-macete-with-minor-premises tr%image-of-domain-is-range)
	    ) )
      (block 
	  (script-comment "`direct-and-antecedent-inference-strategy' at (1)")
	(apply-macete-with-minor-premises tr%injective-composition)
	direct-and-antecedent-inference-strategy
	(apply-macete-with-minor-premises tr%injective-implies-injective-on)
	(apply-macete-with-minor-premises tr%inverse-is-injective)
	)
      (block 
	  (script-comment "`direct-and-antecedent-inference-strategy' at (2)")
	(backchain "with(phi:[zz,ind_1],d,c:zz,zz%interval(c,d)=dom{phi});")
	(backchain "with(psi:[zz,ind_1],b,a:zz,zz%interval(a,b)=dom{psi});")
	(apply-macete-with-minor-premises tr%inverse-composition-image-lemma)
	(weaken (0 1 3 6))
	(cut-with-single-formula
	 "forall(psi:[zz,ind_1],image{psi,dom{psi}}=ran{psi})"
	 )
	(backchain-backwards "with(p:prop,forall(psi:[zz,ind_1],p));")
	(backchain-backwards "with(p:prop,forall(psi:[zz,ind_1],p));")
	(backchain-backwards
	 "with(phi:[zz,ind_1],d,c:zz,zz%interval(c,d)=dom{phi});"
	 )
	(backchain-backwards
	 "with(psi:[zz,ind_1],b,a:zz,zz%interval(a,b)=dom{psi});"
	 )
	simplify
	) )
    (block 
	(script-comment "`force-substitution' at (1)")
      (force-substitution "f oo psi oo ((inverse{psi}) oo phi)"
			  "f oo (psi oo (inverse{psi})) oo phi" (0)
			  )
      (block 
	  (script-comment "`force-substitution' at (0)")
	(apply-macete-with-minor-premises tr%inverse-is-a-right-inverse)
	(apply-macete-with-minor-premises tr%composition-with-id-right)
	(cut-with-single-formula "ran{psi}=ran{phi}")
	(block 
	    (script-comment "`cut-with-single-formula' at (0)")
	  (backchain "with(phi,psi:[zz,ind_1],ran{psi}=ran{phi});")
	  (apply-macete-locally tr%restricted-to-range-composition-lemma (0)
				" f oo phi"
				) )
	(weaken (1 4))
	)
      (block 
	  (script-comment "`force-substitution' at (1)")
	(apply-macete-with-minor-premises tr%associativity-of-composition)
	(apply-macete-with-minor-premises tr%associativity-of-composition)
	) )
    )))

;;;    direct-and-antecedent-inference-strategy
;;;    (force-substitution "f oo phi" "(f oo psi) oo (inverse{psi}  oo phi)" (0))
;;;    (apply-macete-with-minor-premises general-commutative-law-corollary-1)
;;;    direct-and-antecedent-inference-strategy
;;;    (backchain "with(phi:[zz,ind_1],d,c:zz,zz%interval(c,d)=dom{phi});")
;;;    (apply-macete-with-minor-premises tr%domain-composition)
;;;    (cut-with-single-formula "ran{phi}=ran{psi}")
;;;    (backchain "with(psi,phi:[zz,ind_1],ran{phi}=ran{psi});")
;;;    (apply-macete-with-minor-premises tr%inverse-defined-within-range)
;;;    (weaken (0 2 5))
;;;    (cut-with-single-formula "forall(psi:[zz,ind_1],image{psi,dom{psi}}=ran{psi})")
;;;    (backchain-backwards "forall(psi:[zz,ind_1],image{psi,dom{psi}}=ran{psi});")
;;;    (backchain-backwards "forall(psi:[zz,ind_1],image{psi,dom{psi}}=ran{psi}x);")
;;;    (backchain-backwards "with(phi:[zz,ind_1],d,c:zz,zz%interval(c,d)=dom{phi});")
;;;    (backchain-backwards "with(psi:[zz,ind_1],b,a:zz,zz%interval(a,b)=dom{psi});")
;;;    simplify
;;;    (apply-macete-with-minor-premises tr%image-of-domain-is-range)
;;;    (apply-macete-with-minor-premises tr%injective-composition)
;;;    direct-and-antecedent-inference-strategy
;;;    (apply-macete-with-minor-premises tr%injective-implies-injective-on)
;;;    (apply-macete-with-minor-premises tr%inverse-is-injective)
;;;    (backchain "with(phi:[zz,ind_1],d,c:zz,zz%interval(c,d)=dom{phi});")
;;;    (backchain "with(psi:[zz,ind_1],b,a:zz,zz%interval(a,b)=dom{psi});")
;;;    (apply-macete-with-minor-premises tr%inverse-composition-image-lemma)
;;;    (weaken (0 1 3 6))
;;;    (force-substitution "f oo psi oo ((inverse{psi}) oo phi)"
;;;			"f oo (psi oo (inverse{psi})) oo phi" (0))
;;;    (apply-macete-with-minor-premises tr%inverse-is-a-right-inverse)
;;;    (apply-macete-with-minor-premises tr%composition-with-id-right)
;;;    (cut-with-single-formula "ran{psi}=ran{phi}")
;;;    (backchain "with(phi,psi:[zz,ind_1],ran{psi}=ran{phi});")
;;;    (apply-macete-locally tr%restricted-to-range-composition-lemma (0) " f oo phi")
;;;    (weaken (1 4))
;;;    (apply-macete-with-minor-premises tr%associativity-of-composition)
;;;    (apply-macete-with-minor-premises tr%associativity-of-composition)
;;;


(def-theorem monoid-permutation-theorem
  "forall(a,b,c,d:zz, phi:[zz,ind_1], psi:[zz,ind_1], f:[ind_1,uu],s:sets[ind_1],
         zz%interval(c,d) subseteq dom{phi} and
         injective_q{phi} and 
         image{phi,zz%interval(c,d)}=s and
         zz%interval(a,b) subseteq dom{psi} and
         injective_q{psi} and 
         image{psi,zz%interval(a,b)}=s
    implies
     monoid%prod(c,d,f oo phi) == monoid%prod(a,b,f oo psi))"

  (theory monoids-with-index-set)
  (usages transportable-macete)
  (proof
   (


    direct-and-antecedent-inference-strategy
    (force-substitution "monoid%prod(c,d,f oo phi)"
			"monoid%prod(c,d,f oo restrict{phi,zz%interval(c,d)})"
			(0))
    (block 
     (script-comment "node added by `force-substitution' at (0)")
     (force-substitution "monoid%prod(a,b,f oo psi)"
			 "monoid%prod(a,b,f oo restrict{psi,zz%interval(a,b)})"
			 (0))
     (block 
      (script-comment "node added by `force-substitution' at (0)")
      (apply-macete-with-minor-premises general-commutative-law-corollary-2)
      (instantiate-existential ("s"))
      (block 
       (script-comment "node added by `instantiate-existential' at (0 0)")
       (apply-macete-with-minor-premises tr%domain-of-a-restriction)
       simplify
       unfold-defined-constants)
      (apply-macete-with-minor-premises tr%injectivity-of-a-restriction)
      (apply-macete-with-minor-premises tr%image-of-a-restriction)
      (block 
       (script-comment "node added by `instantiate-existential' at (0 3)")
       (apply-macete-with-minor-premises tr%domain-of-a-restriction)
       simplify
       unfold-defined-constants)
      (apply-macete-with-minor-premises tr%injectivity-of-a-restriction)
      (apply-macete-with-minor-premises tr%image-of-a-restriction))
     (block 
      (script-comment "node added by `force-substitution' at (1)")
      (apply-macete-with-minor-premises locality-for-monoid-prod)
      direct-and-antecedent-inference-strategy
      unfold-defined-constants
      (apply-macete-with-minor-premises indicator-facts-macete)
      beta-reduce-repeatedly
      simplify))
    (block 
     (script-comment "node added by `force-substitution' at (1)")
     (apply-macete-with-minor-premises locality-for-monoid-prod)
     direct-and-antecedent-inference-strategy
     unfold-defined-constants
     (apply-macete-with-minor-premises indicator-facts-macete)
     beta-reduce-repeatedly
     simplify)

    )))

(def-theorem characterization-of-monoid%prod%unordered
  "forall(s:sets[ind_1], f:[ind_1,uu],a:uu,
         monoid%prod%unordered(s,f) = a iff 
         forsome(m,n:zz,phi:[zz,ind_1], 
           injective_q{phi} 
             and 
           zz%interval(m,n) subseteq dom{phi}
             and
           image{phi,zz%interval(m,n)} = s
             and 
           a=monoid%prod(m,n,f oo phi)))"
  (theory monoids-with-index-set)
  (proof
   (

    (unfold-single-defined-constant (0) monoid%prod%unordered)
    direct-and-antecedent-inference-strategy
    (contrapose "with(a:uu,p:prop,  iota(a:uu,p)=a)")
    (eliminate-defined-iota-expression 0 w)
    (contrapose "with(f:[ind_1,uu],a:uu,s:sets[ind_1],
  forall(m,n:zz,phi:[zz,ind_1],
    forsome(x_1,x_2:zz,phi(x_1)=phi(x_2) and not(x_1=x_2))
     or 
    forsome(x_$0:zz,
      x_$0 in zz%interval(m,n) and not(x_$0 in dom{phi}))
     or 
    not(image{phi,zz%interval(m,n)}=s)
     or 
    not(a=monoid%prod(m,n,f oo phi))));")
    (backchain-backwards "with(a,w:uu,w=a);")
    (apply-macete-with-minor-premises eliminate-iota-macete)
    direct-and-antecedent-inference-strategy
    (instantiate-existential ("m" "n" "phi"))
    (cut-with-single-formula "b_$0==a")
    (backchain "with(phi:[zz,ind_1],f:[ind_1,uu],n,m:zz,a:uu,
  a=monoid%prod(m,n,f oo phi));")
    (backchain "with(phi_$0:[zz,ind_1],f:[ind_1,uu],n_$0,m_$0:zz,b_$0:uu,
  b_$0=monoid%prod(m_$0,n_$0,f oo phi_$0));")
    (apply-macete-with-minor-premises monoid-permutation-theorem)
    (instantiate-existential ("s"))

    
    )))


(def-theorem value-of-monoid%prod%unordered
  "forall(s:sets[ind_1], f:[ind_1,uu],a:uu,
         monoid%prod%unordered(s,f) = a implies 
         forall(m,n:zz,phi:[zz,ind_1], 
           injective_q{phi} 
             and 
           zz%interval(m,n) subseteq dom{phi}
             and
           image{phi,zz%interval(m,n)} = s
             implies 
           monoid%prod(m,n,f oo phi)=a))"
  (theory monoids-with-index-set)
  (proof
   (

    (apply-macete-with-minor-premises characterization-of-monoid%prod%unordered)
    direct-and-antecedent-inference-strategy
    (backchain "with(u,a:uu,a=u);")
    (cut-with-single-formula
     "monoid%prod(m_$0,n_$0,f oo phi_$0)==monoid%prod(m,n,f oo phi)")
    (apply-macete-with-minor-premises monoid-permutation-theorem)
    (instantiate-existential ("s"))
    )))
