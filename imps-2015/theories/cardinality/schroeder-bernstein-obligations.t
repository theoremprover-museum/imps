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


(herald SCHROEDER-BERNSTEIN-OBLIGATIONS)

(def-theorem SB-SYMMETRY-OBL
  "forall(h_0:[nn,sets[ind_2]],h_1:[nn,sets[ind_1]],
     forall(u_0:nn,
       #(if(u_0=0, 
            dom{g},
            lambda(dummy_$0:sets[ind_1],
              if(#(dummy_$0), image{f,dummy_$0}, ?sets[ind_2]))(h_1(u_0-1))))
         implies 
       if(u_0=0,
          dom{g},
          lambda(dummy_$0:sets[ind_1],
            if(#(dummy_$0), image{f,dummy_$0}, ?sets[ind_2]))(h_1(u_0-1)))=h_0(u_0))
       and 
     forall(u_0:nn,
       #(if(u_0=0,
            dom{f},
            lambda(dummy_$1:sets[ind_2],
              if(#(dummy_$1), image{g,dummy_$1}, ?sets[ind_1]))(h_0(u_0-1))))
         implies 
       if(u_0=0,
          dom{f},
          lambda(dummy_$1:sets[ind_2],
            if(#(dummy_$1), image{g,dummy_$1}, ?sets[ind_1]))(h_0(u_0-1)))=h_1(u_0))
     implies 
       forall(u_0:nn,#(b%seq(u_0)) implies b%seq(u_0)=h_0(u_0))
         and 
       forall(u_0:nn,#(a%seq(u_0)) implies a%seq(u_0)=h_1(u_0)))"
  lemma
  (theory schroeder-bernstein-theory)
  (proof
   (
    (assume-theorem 
     schroeder-bernstein-set-functions-strong-minimality_schroeder-bernstein-theory)
    direct-and-antecedent-inference-strategy
    (backchain "with(p:prop, forall(h_0:[nn,sets[ind_1]],h_1:[nn,sets[ind_2]], p))")
    direct-inference
    auto-instantiate-existential
    (backchain "with(p:prop, forall(h_0:[nn,sets[ind_1]],h_1:[nn,sets[ind_2]], p))")
    direct-inference
    auto-instantiate-existential
    )))

(def-theorem SB->GT2-OBL-1
  "forall(v:[ind_2,ind_1],u:[ind_1,ind_2],b:sets[ind_2],a:sets[ind_1], 
     nonempty_indic_q{a}
      and 
     nonempty_indic_q{b}
      and 
     dom{u}=a
      and 
     dom{v}=b
      and 
     ran{u} subseteq b
      and 
     ran{v} subseteq a
      and 
     injective_on_q{u,a}
      and 
     injective_on_q{v,b}
      implies 
     forall(x_$0:ind_1,
       if_form(x_$0 in a,
         #(u(x_$0)) implies u(x_$0) in b,
         not(#(u(x_$0))))))"
  lemma
  (theory generic-theory-2)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises tr%element-of-a-subset-is-an-element)
    auto-instantiate-existential
    (apply-macete-with-minor-premises range-domain-membership)
    (apply-macete-with-minor-premises domain-membership-iff-defined)
    (apply-macete-with-minor-premises rev%domain-membership-iff-defined)
    (backchain "with(a:sets[ind_1],u:[ind_1,ind_2],dom{u}=a)")
    )))

(def-theorem SB->GT2-OBL-2
  "forall(v:[ind_2,ind_1],u:[ind_1,ind_2],b:sets[ind_2],a:sets[ind_1], 
     nonempty_indic_q{a}
      and 
     nonempty_indic_q{b}
      and 
     dom{u}=a
      and 
     dom{v}=b
      and 
     ran{u} subseteq b
      and 
     ran{v} subseteq a
      and 
     injective_on_q{u,a}
      and 
     injective_on_q{v,b}
      implies 
     forall(x_$0:ind_2,
       if_form(x_$0 in b,
         #(v(x_$0)) implies v(x_$0) in a,
         not(#(v(x_$0))))))"
  lemma
  (theory generic-theory-2)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises tr%element-of-a-subset-is-an-element)
    auto-instantiate-existential
    (apply-macete-with-minor-premises tr%range-domain-membership)
    (apply-macete-with-minor-premises tr%domain-membership-iff-defined)
    (apply-macete-with-minor-premises tr%rev%domain-membership-iff-defined)
    (backchain "with(b:sets[ind_2],v:[ind_2,ind_1],dom{v}=b)")
    )))

(def-theorem SB->GT2-OBL-3
  "forall(v:[ind_2,ind_1],u:[ind_1,ind_2],b:sets[ind_2],a:sets[ind_1], 
     nonempty_indic_q{a}
      and 
     nonempty_indic_q{b}
      and 
     dom{u}=a
      and 
     dom{v}=b
      and 
     ran{u} subseteq b
      and 
     ran{v} subseteq a
      and 
     injective_on_q{u,a}
      and 
     injective_on_q{v,b}
      implies 
     forall(x_0:ind_1,x_0 in a implies #(u(x_0))))"
  lemma
  (theory generic-theory-2)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises rev%domain-membership-iff-defined)
    (backchain "with(a:sets[ind_1],u:[ind_1,ind_2],dom{u}=a)")
    )))

(def-theorem SB->GT2-OBL-4
  "forall(v:[ind_2,ind_1],u:[ind_1,ind_2],b:sets[ind_2],a:sets[ind_1], 
     nonempty_indic_q{a}
      and 
     nonempty_indic_q{b}
      and 
     dom{u}=a
      and 
     dom{v}=b
      and 
     ran{u} subseteq b
      and 
     ran{v} subseteq a
      and 
     injective_on_q{u,a}
      and 
     injective_on_q{v,b}
      implies 
     forall(x_0:ind_2,x_0 in b implies #(v(x_0))))"
  lemma
  (theory generic-theory-2)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises tr%rev%domain-membership-iff-defined)
    (backchain "with(b:sets[ind_2],v:[ind_2,ind_1],dom{v}=b)")
    )))

(def-theorem SB->GT2-OBL-5
  "forall(v:[ind_2,ind_1],u:[ind_1,ind_2],b:sets[ind_2],a:sets[ind_1], 
     nonempty_indic_q{a}
      and 
     nonempty_indic_q{b}
      and 
     dom{u}=a
      and 
     dom{v}=b
      and 
     ran{u} subseteq b
      and 
     ran{v} subseteq a
      and 
     injective_on_q{u,a}
      and 
     injective_on_q{v,b}
      implies 
     forall(x_1,x_2:ind_1,
       x_1 in a and x_2 in a
        implies 
       (u(x_1)=u(x_2) implies x_1=x_2)))"
  lemma
  (theory generic-theory-2)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (backchain "with(u:[ind_1,ind_2],a:sets[ind_1],injective_on_q{u,a})")
    direct-inference
    )))

(def-theorem SB->GT2-OBL-6
  "forall(v:[ind_2,ind_1],u:[ind_1,ind_2],b:sets[ind_2],a:sets[ind_1], 
     nonempty_indic_q{a}
      and 
     nonempty_indic_q{b}
      and 
     dom{u}=a
      and 
     dom{v}=b
      and 
     ran{u} subseteq b
      and 
     ran{v} subseteq a
      and 
     injective_on_q{u,a}
      and 
     injective_on_q{v,b}
      implies 
     forall(x_1,x_2:ind_2,
       x_1 in b and x_2 in b
        implies 
       (v(x_1)=v(x_2) implies x_1=x_2)))"
  lemma
  (theory generic-theory-2)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (backchain "with(v:[ind_2,ind_1],b:sets[ind_2],injective_on_q{v,b})")
    direct-inference
    )))


