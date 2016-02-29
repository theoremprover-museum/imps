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


(herald partition-lemmas)


(include-files
  (files (imps theories/cardinality/finite-cardinality)))



(def-theorem F-CARD-ZERO-PARTITION-LEMMA
  "forall(p:sets[sets[ind_1]],s:sets[ind_1],
     (partition_q{p,s} and f_card{p}=0) implies f_card{s}=0)"
  (theory generic-theory-1)
  (usages transportable-macete)
  (proof
   (
    (apply-macete-with-minor-premises tr%empty-indic-has-f-card-zero)
    direct-and-antecedent-inference-strategy
    (weaken (1))
    (contrapose "with(p:prop, forall(x:ind_1,p))")
    (backchain "with(p,q:sets[sets[ind_1]],p=q)")
    (weaken (1))
    simplify
    (contrapose "with(p:prop, p)")
    extensionality
    beta-reduce-repeatedly
    )))


;;; Finite cardinality of a disjoint union

(def-theorem F-CARD-DISJOINT-UNION-LEMMA-1
  "forall(n_$0:nn,f_$0,f:[ind_1,nn],
     dom{lambda(a_$1:ind_1,
       if(a_$1 in dom{f},
          f(a_$1),
          a_$1 in dom{f_$0},
          n_$0+f_$0(a_$1),
          ?nn))}
     =dom{f} union dom{f_$0})"
  lemma
  (theory generic-theory-1)
  (proof
   (
    direct-inference
    extensionality
    direct-inference
    beta-reduce-repeatedly
    (apply-macete-with-minor-premises tr%domain-membership-iff-defined)
    (raise-conditional (0))
    simplify
    (raise-conditional (0))
    simplify
    )))


  
(def-theorem F-CARD-DISJOINT-UNION-LEMMA-2
  "forall(n,n_$0:nn,f_$0,f:[ind_1,nn],
     ran{f}=omega(n_$0) and ran{f_$0}=omega(n) and dom{f} disj dom{f_$0}
      implies
     indic{y_$1:nn,
       forsome(x_$5:ind_1,
         y_$1=lambda(a_$1:ind_1,
                if(a_$1 in dom{f},
                   f(a_$1),
                   a_$1 in dom{f_$0},
                   n_$0+f_$0(a_$1),
                   ?nn))(x_$5))}
     =omega(n_$0+n))"
  lemma
  (theory generic-theory-1)
  (proof 
   (
    (apply-macete-with-minor-premises tr%domain-membership-iff-defined)
    simplify
    (raise-conditional (0))
    simplify
    direct-and-antecedent-inference-strategy
    extensionality
    simplify
    direct-and-antecedent-inference-strategy
    (block 
     (script-comment 
      "node added by `direct-and-antecedent-inference-strategy' at (0 0 0 0)")
     (apply-macete-with-minor-premises finite-cardinal-application)
     (backchain "with(n,x_0:nn,x_0=n);")
     (cut-with-single-formula "f(x_$5)<n_$0")
     simplify
     (block 
      (script-comment "node added by `cut-with-single-formula' at (1)")
      (apply-macete-with-minor-premises rev%finite-cardinal-members-are-<)
      (backchain-backwards "with(n_$0:nn,f:[ind_1,nn],ran{f}=omega(n_$0));")
      beta-reduce-insistently
      simplify
      auto-instantiate-existential))
    (block 
     (script-comment 
      "node added by `direct-and-antecedent-inference-strategy' at (0 0 0 1 0)")
     (apply-macete-with-minor-premises finite-cardinal-application)
     (backchain "with(r:rr,x_0:nn,x_0=r);")
     (weaken (0))
     simplify
     (apply-macete-with-minor-premises rev%finite-cardinal-members-are-<)
     (backchain-backwards "with(n:nn,f_$0:[ind_1,nn],ran{f_$0}=omega(n));")
     simplify-insistently
     (instantiate-existential ("x_$5")))
    (block 
     (script-comment 
      "node added by `direct-and-antecedent-inference-strategy' at (0 1)")
     (case-split ("x_0<n_$0"))
     (block 
      (script-comment "node added by `case-split' at (1)")
      (contrapose "with(n_$0:nn,f:[ind_1,nn],ran{f}=omega(n_$0));")
      extensionality
      (instantiate-existential ("x_0"))
      (apply-macete-with-minor-premises finite-cardinal-application)
      simplify
      direct-inference
      (contrapose "with(p:prop,not(p));")
      (instantiate-existential ("x")))
     (block 
      (script-comment "node added by `case-split' at (2)")
      (contrapose "with(n:nn,f_$0:[ind_1,nn],ran{f_$0}=omega(n));")
      extensionality
      (instantiate-existential ("x_0-n_$0"))
      (apply-macete-with-minor-premises finite-cardinal-application)
      simplify
      direct-inference
      (contrapose "with(p:prop,not(forsome(x_$5:ind_1,p)));")
      (instantiate-existential ("x"))
      (contrapose "with(n:nn,#(n));")
      (apply-macete-with-minor-premises tr%rev%domain-membership-iff-defined)
      (backchain "with(f:sets[ind_1],f disj f);")
      (apply-macete-with-minor-premises tr%domain-membership-iff-defined)))
    )))

(def-theorem F-CARD-DISJOINT-UNION-LEMMA-3
  "forall(n,n_$0:nn,f_$0,f:[ind_1,nn],
     injective_on_q{f,dom{f}} and 
     injective_on_q{f_$0,dom{f_$0}} and
     ran{f}=omega(n_$0) and 
     ran{f_$0}=omega(n) and 
     dom{f} disj dom{f_$0}
      implies
     injective_on_q{lambda(a:ind_1,
                      if(a in dom{f},
                         f(a),
                         a in dom{f_$0},
                         n_$0+f_$0(a),
                         ?nn)),
                    dom{f} union dom{f_$0}})"
  lemma
  (theory generic-theory-1)
  (proof				; 107 nodes
   (
    direct-and-antecedent-inference-strategy
    insistent-direct-inference
    beta-reduce-repeatedly
    (force-substitution 
     "x_$0 in dom{f} union dom{f_$0}" 
     "(x_$0 in dom{f}) or (x_$0 in dom{f_$0})" (0))
    (force-substitution 
     "x_$1 in dom{f} union dom{f_$0}" 
     "(x_$1 in dom{f}) or (x_$1 in dom{f_$0})" (0))
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "f(x_$0)=f(x_$1)")
    (backchain "with(f:[ind_1,nn],injective_on_q{f,dom{f}})")
    direct-inference
    (weaken (3 4 5 6 7))
    (incorporate-antecedent "with(m,n:nn, m=n)")
    simplify
    (instantiate-universal-antecedent 
     "with(a,b:sets[ind_1], a disj b)" ("x_$0"))
    (cut-with-single-formula "n_$0+f_$0(x_$0)=f(x_$1)")
    (cut-with-single-formula "f(x_$1)<n_$0")
    (weaken (2 3 4 5 6 7 8 9))
    (contrapose "with(n_$0:nn,x_$1:ind_1,f:[ind_1,nn],f(x_$1)<n_$0)")
    (backchain-backwards "with(m,n:nn, m=n)")
    simplify
    (apply-macete-with-minor-premises rev%finite-cardinal-members-are-<)
    (backchain-backwards "with(n_$0:nn,f:[ind_1,nn],ran{f}=omega(n_$0))")
    (apply-macete-with-minor-premises tr%range-domain-membership)
    (weaken (4 5 6 7))
    (contrapose "with(m,n:nn, m=n)")
    (case-split-on-conditionals (2))
    (apply-macete-with-minor-premises tr%rev%domain-membership-iff-defined)
    (raise-conditional (0))
    (contrapose "with(p:prop, not(p))")
    (antecedent-inference "with(p,q,r:prop, if_form(p,q,r))")
    (instantiate-universal-antecedent 
     "with(a,b:sets[ind_1], a disj b)" ("x_$1"))
    (cut-with-single-formula "n_$0+f_$0(x_$1)=f(x_$0)")
    (cut-with-single-formula "f(x_$0)<n_$0")
    (weaken (2 3 4 5 6 7 8 9))
    (contrapose "with(n_$0:nn,x_$0:ind_1,f:[ind_1,nn],f(x_$0)<n_$0)")
    (backchain-backwards "with(m,n:nn, m=n)")
    simplify
    (apply-macete-with-minor-premises rev%finite-cardinal-members-are-<)
    (backchain-backwards "with(n_$0:nn,f:[ind_1,nn],ran{f}=omega(n_$0))")
    (apply-macete-with-minor-premises tr%range-domain-membership)
    (weaken (4 5 6 7))
    (contrapose "with(m,n:nn, m=n)")
    (case-split-on-conditionals (2))
    (instantiate-universal-antecedent-multiply 
     "with(f:sets[ind_1],f disj f);"
     (("x_$0") ("x_$1")))
    (cut-with-single-formula "n_$0+f_$0(x_$0)=n_$0+f_$0(x_$1)")
    (backchain "with(f_$0:[ind_1,nn],injective_on_q{f_$0,dom{f_$0}})")
    direct-inference
    (weaken (1 2 3 4 5 6 7 8 9))
    (contrapose "with(p:prop, p)")
    simplify
    (weaken (1 2 3 4))
    (incorporate-antecedent "with(m,n:nn, m=n)")
    (case-split-on-conditionals (0))
    (apply-macete-with-minor-premises tr%rev%domain-membership-iff-defined)
    (raise-conditional (0))
    direct-and-antecedent-inference-strategy
    (weaken (1 2 3 4))
    (weaken (0 1 2 3 4 5))
    simplify-insistently
    (weaken (0 1 2 3 4))
    simplify-insistently
    )))

(def-theorem F-CARD-DISJOINT-UNION
  "forall(u,v:sets[ind_1], 
     u disj v and f_indic_q{u} and f_indic_q{v} implies
     f_card{u union v} = f_card{u} + f_card{v})"
  (theory generic-theory-1)
  (usages transportable-macete)
  (proof				; 68 nodes
   (
    (apply-macete-with-minor-premises iota-free-definition-of-f-indic-q)
    direct-and-antecedent-inference-strategy
    (backchain "with(n_$0:nn,u:sets[ind_1],f_card{u}=n_$0)")
    (backchain "with(n:nn,v:sets[ind_1],f_card{v}=n)")
    (apply-macete-with-minor-premises iota-free-definition-of-f-card)
    (cut-with-single-formula "u equinumerous omega(n_$0)")
    (cut-with-single-formula "v equinumerous omega(n)")
    (weaken (2 3))
    (antecedent-inference-strategy (0 1))
    (instantiate-existential 
     ("lambda(a:ind_1,if(a in u, f(a), if(a in v, n_$0+f_$0(a), ?nn)))"))
    (backchain-backwards "with(u:sets[ind_1],f:[ind_1,nn],dom{f}=u)")
    (backchain-backwards "with(u:sets[ind_1],f:[ind_1,nn],dom{f}=u)")
    (backchain-backwards "with(v:sets[ind_1],f_$0:[ind_1,nn],dom{f_$0}=v)")
    (backchain-backwards "with(v:sets[ind_1],f_$0:[ind_1,nn],dom{f_$0}=v)")
    (weaken (0 1 2 3 4 5 6))
    (apply-macete-with-minor-premises f-card-disjoint-union-lemma-1)
    (cut-with-single-formula "dom{f} disj dom{f_$0}")
    (backchain-backwards "with(u:sets[ind_1],f:[ind_1,nn],dom{f}=u)")
    (backchain-backwards "with(v:sets[ind_1],f_$0:[ind_1,nn],dom{f_$0}=v)")
    (weaken (1 3 4 5 6 8))
    (apply-macete-with-minor-premises f-card-disjoint-union-lemma-2)
    simplify
    (backchain "with(v:sets[ind_1],f_$0:[ind_1,nn],dom{f_$0}=v)")
    (backchain "with(u:sets[ind_1],f:[ind_1,nn],dom{f}=u)")
    (incorporate-antecedent "with(v,u:sets[ind_1],u disj v)")
    (backchain-backwards "with(u:sets[ind_1],f:[ind_1,nn],dom{f}=u)")
    (backchain-backwards "with(u:sets[ind_1],f:[ind_1,nn],dom{f}=u)")
    (backchain-backwards "with(u:sets[ind_1],f:[ind_1,nn],dom{f}=u)")
    (backchain-backwards "with(v:sets[ind_1],f_$0:[ind_1,nn],dom{f_$0}=v)")
    (backchain-backwards "with(v:sets[ind_1],f_$0:[ind_1,nn],dom{f_$0}=v)")
    (backchain-backwards "with(v:sets[ind_1],f_$0:[ind_1,nn],dom{f_$0}=v)")
    (apply-macete-with-minor-premises f-card-disjoint-union-lemma-3)
    direct-inference
    (instantiate-existential ("n"))
    simplify
    simplify
    (weaken (0 1 2 3 4 5 6))
    sort-definedness
    direct-inference
    simplify
    (case-split-on-conditionals (0))
    (incorporate-antecedent "with(n:nn,v:sets[ind_1],f_card{v}=n)")
    (apply-macete-with-minor-premises iota-free-definition-of-f-card)
    (incorporate-antecedent "with(n_$0:nn,u:sets[ind_1],f_card{u}=n_$0)")
    (apply-macete-with-minor-premises iota-free-definition-of-f-card)
    )))



;;; Finiteness of a partition

(def-theorem FINITENESS-OF-A-PARTITION-LEMMA
  "forall(p:sets[sets[ind_1]],s:sets[ind_1], 
     partition_q{p,s} and 
     f_indic_q{s} and
     forall(u:sets[ind_1], u in p implies nonempty_indic_q{u})
      implies 
     f_indic_q{p})"
  lemma
  (theory generic-theory-1)
  (proof
   (


    direct-inference
    direct-inference
    (antecedent-inference "with(p:prop,p);")
    (cut-with-single-formula "f_card{p}<=f_card{s}")
    (apply-macete-with-minor-premises tr%f-card-leq-iff-finite-and-embeds)
    direct-inference
    (cut-with-single-formula
     "forsome(g:[sets[ind_1],ind_1], 
        forall(z:sets[ind_1], z in p implies g(z) in z))"
     )
    (move-to-sibling 1)
    choice-principle
    (antecedent-inference "with(p:prop,forsome(g:[sets[ind_1],ind_1],p));")
    (instantiate-existential ("restrict{g,p}"))
    (block 
      (script-comment "`instantiate-existential' at (0 0)") extensionality
      simplify-insistently direct-and-antecedent-inference-strategy simplify
      (contrapose "with(p:prop,not(p));")
      (auto-instantiate-universal-antecedent
       "with(g:[sets[ind_1],ind_1],p:sets[sets[ind_1]],
            forall(z:sets[ind_1],z in p implies g(z) in z));"
       ) )
    (block 
      (script-comment "`instantiate-existential' at (0 1)") simplify-insistently
      direct-and-antecedent-inference-strategy
      (backchain "with(s:sets[ind_1],p:sets[sets[ind_1]],partition_q{p,s});")
      auto-instantiate-existential simplify
      )
    simplify-insistently
    insistent-direct-and-antecedent-inference-strategy
    (antecedent-inference "with(s:sets[ind_1],p:sets[sets[ind_1]],partition_q{p,s});")
    (instantiate-universal-antecedent "with(p:prop,forall(u,v:sets[ind_1],p));" ("x_$0" "x_$6"))
    (instantiate-universal-antecedent "with(x_$6,x_$0:sets[ind_1],x_$0 disj x_$6);" ("g(x_$0)"))
    (auto-instantiate-universal-antecedent
     "with(g:[sets[ind_1],ind_1],p:sets[sets[ind_1]],  
            forall(z:sets[ind_1],z in p implies g(z) in z));"
     )
    (auto-instantiate-universal-antecedent
     "with(g:[sets[ind_1],ind_1],p:sets[sets[ind_1]],
              forall(z:sets[ind_1],z in p implies g(z) in z));"
     )
    (contrapose "with(p:prop,not(p));")
    (backchain "with(i:ind_1,i=i);")
    (move-to-ancestor 5)
    (block 
      (script-comment "`instantiate-universal-antecedent' at (0 0 1)")
      (contrapose "with(p:prop,not(p));") (backchain "with(i:ind_1,i=i);")
      (contrapose
       "with(i:ind_1,p:sets[sets[ind_1]],
  forall(z:sets[ind_1],z in p implies i in z));"
       )
      auto-instantiate-existential
      )
    )))


;direct-inference
;    direct-inference
;    (antecedent-inference "with(p:prop,p);")
;    (cut-with-single-formula "f_card{p}<=f_card{s}")
;    (apply-macete-with-minor-premises tr%f-card-leq-iff-finite-and-embeds)
;    direct-inference
;    (cut-with-single-formula 
;     "forsome(g:[sets[ind_1],ind_1], 
;        forall(z:sets[ind_1], z in p implies g(z) in z))")
;    (move-to-sibling 1)
;    choice-principle
;    (block 
;      (script-comment "node added by `cut-with-single-formula' at (0)")
;      (antecedent-inference "with(p:prop,forsome(g:[sets[ind_1],ind_1],p));")
;      (instantiate-existential ("restrict{g,p}"))
;      (block 
;	(script-comment "node added by `instantiate-existential' at (0 0)")
;	extensionality
;	simplify-insistently
;	direct-and-antecedent-inference-strategy
;	simplify
;	(contrapose "with(p:prop,not(p));")
;	(auto-instantiate-universal-antecedent 
;	 "with(g:[sets[ind_1],ind_1],p:sets[sets[ind_1]],
;            forall(z:sets[ind_1],z in p implies g(z) in z));"))
;      (block 
;	(script-comment "node added by `instantiate-existential' at (0 1)")
;	simplify-insistently
;	direct-and-antecedent-inference-strategy
;	(backchain "with(s:sets[ind_1],p:sets[sets[ind_1]],partition_q{p,s});")
;	auto-instantiate-existential
;	simplify)
;      (block 
;	(script-comment "node added by `instantiate-existential' at (0 2)")
;	simplify-insistently
;	insistent-direct-and-antecedent-inference-strategy
;	(antecedent-inference 
;	 "with(s:sets[ind_1],p:sets[sets[ind_1]],partition_q{p,s});")
;	(instantiate-universal-antecedent 
;	 "with(p:prop,forall(u,v:sets[ind_1],p));" ("x_$0" "x_$6"))
;	(instantiate-universal-antecedent 
;	 "with(x_$6,x_$0:sets[ind_1],x_$0 disj x_$6);" ("g(x_$0)"))
;	(auto-instantiate-universal-antecedent 
;	 "with(g:[sets[ind_1],ind_1],p:sets[sets[ind_1]],  
;            forall(z:sets[ind_1],z in p implies g(z) in z));")
;	(block 
;	  (script-comment 
;	   "node added by `instantiate-universal-antecedent' at (0 0 1)")
;	  (auto-instantiate-universal-antecedent 
;	   "with(g:[sets[ind_1],ind_1],p:sets[sets[ind_1]],
;              forall(z:sets[ind_1],z in p implies g(z) in z));")
;	  (contrapose "with(p:prop,not(p));")
;	  (backchain "with(i:ind_1,i=i);"))))
    

(def-theorem FINITENESS-OF-A-PARTITION
  "forall(p:sets[sets[ind_1]],s:sets[ind_1], 
     partition_q{p,s} and f_indic_q{s} implies f_indic_q{p})"
  (theory generic-theory-1)
  (usages transportable-macete)
  (proof				; 101 nodes
   (
    direct-inference-strategy
    (case-split ("forall(u:sets[ind_1], u in p implies nonempty_indic_q{u})"))
    (antecedent-inference "with(p,q:prop, p and q)")
    (antecedent-inference 
     "with(s:sets[ind_1],p:sets[sets[ind_1]],partition_q{p,s})")
    (apply-macete-with-minor-premises finiteness-of-a-partition-lemma)
    (instantiate-existential ("s"))
    (cut-with-single-formula "empty_indic{ind_1} in p")
    (cut-with-single-formula 
     "forsome(q:sets[sets[ind_1]],q = p diff singleton{empty_indic{ind_1}})")
    (antecedent-inference "with(p:prop, forsome(q:sets[sets[ind_1]],p))")
    (cut-with-single-formula "f_indic_q{q}")
    (force-substitution "p" "q union singleton{empty_indic{ind_1}}" (0))
    (apply-macete-with-minor-premises tr%iota-free-definition-of-f-indic-q)
    (apply-macete-with-minor-premises tr%f-card-disjoint-union)
    (instantiate-existential ("f_card{q}+1"))
    simplify
    (apply-macete-with-minor-premises tr%singleton-has-f-card-one)
    (instantiate-existential ("empty_indic{ind_1}"))
    (apply-macete-with-minor-premises tr%iota-free-definition-of-f-indic-q)
    (instantiate-existential ("1"))
    (backchain "with(p,q:sets[sets[ind_1]],p=q)")
    (apply-macete-with-minor-premises tr%diff-with-indic-is-disj-from-indic)
    (backchain "with(p,q:sets[sets[ind_1]],p=q)")
    (cut-with-single-formula " singleton{empty_indic{ind_1}} subseteq p")
    (apply-macete-with-minor-premises tr%diff-union-equal-whole)
    insistent-direct-inference
    (apply-macete-with-minor-premises tr%in-singleton-iff-equals-single-member)
    simplify
    (cut-with-single-formula "partition_q{q,s}")
    (apply-macete-with-minor-premises finiteness-of-a-partition-lemma)
    (antecedent-inference 
     "with(s:sets[ind_1],q:sets[sets[ind_1]],partition_q{q,s})")
    (instantiate-existential ("s"))
    (force-substitution "nonempty_indic_q{u}" "not(empty_indic_q{u})" (0))
    (instantiate-transported-theorem equals-empty-indic-iff-empty () ("u"))
    (contrapose "with(u:sets[ind_1],q:sets[sets[ind_1]],u in q)")
    (backchain "with(u:sets[ind_1],u=empty_indic{ind_1})")
    (backchain "with(p,q:sets[sets[ind_1]],p=q)")
    (weaken (0 1 2 3 4 5 6 7 8))
    simplify-insistently
    (backchain "with(p,q:sets[sets[ind_1]],p=q)")
    (force-substitution "s" "s diff empty_indic{ind_1}" (0))
    (apply-macete-with-minor-premises tr%decremented-partition-lemma)
    (antecedent-inference "with(p,q:prop, p and q)")
    (antecedent-inference 
     "with(s:sets[ind_1],p:sets[sets[ind_1]],partition_q{p,s})")
    direct-and-antecedent-inference-strategy
    insistent-direct-inference
    extensionality
    direct-inference
    (weaken (0 1 2 3 4 5))
    simplify-insistently
    (case-split-on-conditionals (0))
    (instantiate-existential ("p diff singleton{empty_indic{ind_1}}"))
    (weaken (1))
    (contrapose "with(p:prop, not(p))")
    direct-and-antecedent-inference-strategy
    (force-substitution "nonempty_indic_q{u}" "not(empty_indic_q{u})" (0))
    (instantiate-transported-theorem equals-empty-indic-iff-empty () ("u"))
    (contrapose "with(p:prop, not(p))")
    simplify
    )))


;;; Finite uniform partition theorem

(def-theorem FINITE-UNIFORM-PARTITION-LEMMA
  "forall(n:zz, 0<=n implies
     forall(p:sets[sets[ind_1]],s:sets[ind_1],m:nn,
       (partition_q{p,s} and 
       f_card{p}=n and 
       forall(u:sets[ind_1], (u in p) implies f_card{u} = m))
         implies f_card{s} = m * n))"
  lemma
  (theory generic-theory-1)
  (proof
   (
    (apply-macete-with-minor-premises integer-induction)
    beta-reduce-repeatedly
    direct-inference
    direct-inference
    direct-inference
    (force-substitution "m*0" "0" (0))
    (apply-macete-with-minor-premises f-card-zero-partition-lemma)
    simplify
    (weaken (0))
    direct-inference
    direct-inference
    direct-inference
    direct-inference
    direct-inference
    (antecedent-inference "with(p,q,r:prop, p and q and r)")
    (cut-with-single-formula "nonempty_indic_q{p}")
    (antecedent-inference "with(p:sets[sets[ind_1]],nonempty_indic_q{p})")
    (cut-with-single-formula "partition_q{p diff singleton{x},s diff x}")
    (cut-with-single-formula "f_card{s diff x}=m*t")
    (weaken (6))
    (instantiate-universal-antecedent 
     "with(p:prop,forall(u:sets[ind_1],p))" ("x"))
    (force-substitution "s" "(s diff x) union x" (0))
    (apply-macete-with-minor-premises f-card-disjoint-union)
    (backchain "with(m:nn,x:sets[ind_1],f_card{x}=m)")
    (backchain "with(t:zz,m:nn,x,s:sets[ind_1],f_card{s diff x}=m*t)")
    (weaken (0 1 2 3 4 5))
    simplify
    (weaken (0 1 2 3 4 5 6))
    simplify-insistently
    (apply-macete-with-minor-premises tr%diff-union-equal-whole)
    (antecedent-inference-strategy (1))
    insistent-direct-inference-strategy
    (backchain "with(p,q:prop, forall(x:ind_1,p iff q))")
    auto-instantiate-existential
    (instantiate-universal-antecedent 
     "with(q:prop, forall(p:sets[sets[ind_1]], s:sets[ind_1],m:nn,q))" 
     ("p diff singleton{x}" "s diff x" "m"))
    (contrapose "with(p:prop, not(p))")
    (cut-with-single-formula "f_indic_q{p diff singleton{x}}")
    (cut-with-single-formula "f_card{singleton{x}}=1")
    (cut-with-single-formula 
     "f_card{p}=f_card{p diff singleton{x}}+f_card{singleton{x}}")
    (backchain "with(t:zz,p:sets[sets[ind_1]],f_card{p}=t+1)")
    (incorporate-antecedent 
     "with(x:sets[ind_1],p:sets[sets[ind_1]],
        f_card{p}=f_card{p diff singleton{x}}+f_card{singleton{x}})")
    (backchain "with(t:zz,p:sets[sets[ind_1]],f_card{p}=t+1)")
    (backchain "with(x:sets[ind_1],f_card{singleton{x}}=1)")
    (weaken (0 1 2 3 4 5 6 7 8))
    simplify
    (force-substitution "p" "(p diff singleton{x}) union singleton{x}" (0))
    (apply-macete-with-minor-premises tr%f-card-disjoint-union)
    simplify
    (weaken (0 1 2 3 4 5 6 7 8))
    simplify-insistently
    (apply-macete-with-minor-premises tr%diff-union-equal-whole)
    insistent-direct-inference
    beta-reduce-insistently
    (case-split-on-conditionals (0))
    (apply-macete-with-minor-premises tr%singleton-has-f-card-one)
    (instantiate-existential ("x"))
    (apply-macete-with-minor-premises tr%subset-of-finite-indic-is-finite)
    (instantiate-existential ("p"))
    insistent-direct-inference
    beta-reduce-insistently
    (case-split-on-conditionals (0))
    (contrapose "with(p:prop, not(p))")
    (backchain "with(p:prop, forall(u:sets[ind_1],p))")
    (incorporate-antecedent "with(x:sets[ind_1],a:sets[sets[ind_1]], x in a)")
    beta-reduce-insistently
    (case-split-on-conditionals (0))
    (apply-macete-with-minor-premises tr%decremented-partition-lemma)
    (weaken (1 2 4 5))
    (antecedent-inference-strategy (0))
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises tr%rev%positive-f-card-iff-nonempty)
    (weaken (0 2 3))
    simplify
    )))

(def-theorem FINITE-UNIFORM-PARTITION-THEOREM
  "forall(p:sets[sets[ind_1]],s:sets[ind_1],m:nn,
     (partition_q{p,s} and 
     f_indic_q{s} and
     forall(u:sets[ind_1], (u in p) implies f_card{u} = m))
       implies f_card{s} = m * f_card{p})"
  (theory generic-theory-1)
  (usages transportable-macete)
  (proof
   (
    direct-inference-strategy
    (antecedent-inference "with(p,q,r,s:prop, p and q and r)")
    (cut-with-single-formula "f_indic_q{p}")
    (instantiate-theorem finite-uniform-partition-lemma ("f_card{p}"))
    (simplify-antecedent "with(p:prop, not(p))")
    (backchain 
     "with(x:prop, forall(p:sets[sets[ind_1]],s:sets[ind_1],m:nn,x))")
    auto-instantiate-existential
    (apply-macete-with-minor-premises finiteness-of-a-partition)
    (antecedent-inference 
     "with(s:sets[ind_1],p:sets[sets[ind_1]],partition_q{p,s})")
    auto-instantiate-existential
    )))

