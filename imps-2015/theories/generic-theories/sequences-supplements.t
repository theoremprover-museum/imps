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


(herald sequences-supplements)

(include-files 
 (files (imps theories/generic-theories/sequences)))

;;;(set (proof-log-port) (standard-output))

(def-theorem drop-sequence-lemma
  "forall(s:[nn,ind_1], #(s(0)) and f_seq_q{drop{s,1}} implies f_seq_q{s})"
  (theory sequences)
  (proof
   (


    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "s=cons{s(0),drop{s,1}}")
    (block 
      (script-comment "`cut-with-single-formula' at (0)")
      (backchain "with(f,s:[nn,ind_1],s=f);")
      (apply-macete-with-minor-premises cons-fseq-biconditional))
    (apply-macete-with-minor-premises cons-car-cdr-lemma)

    )))


(def-theorem length-of-drop-one
  "forall(s:[nn -> ind_1], n:nn, 
           #(s(0)) 
              implies 
           (length{s} <=n+1 iff length{drop{s,1}}<=n))"
  reverse
  (usages transportable-macete)
  (theory sequences)
  (proof
   (


    direct-and-antecedent-inference-strategy
    (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (0 0 0)")
      (apply-macete-with-minor-premises length-of-drop)
      (case-split-on-conditionals (0)))
    (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (0 0 1)")
      (cut-with-single-formula "f_seq_q{s}")
      (move-to-sibling 1)
      (block 
	(script-comment "`cut-with-single-formula' at (1)")
	(apply-macete-with-minor-premises drop-sequence-lemma)
	direct-inference)
      (block 
	(script-comment "`cut-with-single-formula' at (0)")
	(contrapose "with(n:nn,n<=n);")
	(apply-macete-with-minor-premises length-of-drop)
	(cut-with-single-formula "0<length{s}")
	simplify
	(apply-macete-with-minor-premises meaning-of-length)))

    )))


;;;Collapsing and constriction of finite sequences:

(load-section basic-cardinality)

(def-quasi-constructor collapse
  "lambda(f:[nn,ind_1], lambda(n:nn, f (omega%embedding(dom{f})(n))))"
  (language sequences)
  (fixed-theories h-o-real-arithmetic))

(def-theorem length-of-collapse-lemma
  "forall(s:[nn,ind_1], 
        forall(m:nn, forall(k:nn, m<=k implies not(#(s(k))))
          implies
        length(collapse{s})<=m))"
  (theory sequences)
  (usages transportable-macete)
  (proof
   (


    direct-and-antecedent-inference-strategy
    (cut-with-single-formula
     "forsome(k:nn, k<=m and dom{omega%embedding(dom{s})}=omega(k))")
    (move-to-sibling 1)
    (block 
      (script-comment "`cut-with-single-formula' at (1)")
      (apply-macete-with-minor-premises dom-of-omega%embedding-at-finite-set)
      simplify-insistently
      direct-and-antecedent-inference-strategy
      (instantiate-universal-antecedent "with(p:prop,forall(k:nn,p));" ("x"))
      simplify)
    (block 
      (script-comment "`cut-with-single-formula' at (0)")
      (antecedent-inference "with(p:prop,forsome(k:nn,p));")
      (incorporate-antecedent "with(p:prop,p and p);")
      (unfold-single-defined-constant (0) omega)
      (force-substitution "dom{omega%embedding(dom{s})}=indic{m:nn,  m<k}"
			  "forall(p:nn, #(omega%embedding(dom{s})(p)) iff p<k)"
			  (0))
      (move-to-sibling 1)
      (block 
	(script-comment "`force-substitution' at (1)")
	(force-substitution "p<k" "p in indic{m:nn,  m<k}" (0))
	(move-to-sibling 1)
	(block 
	  (script-comment "`force-substitution' at (1)")
	  (apply-macete-with-minor-premises indicator-facts-macete)
	  beta-reduce-repeatedly)
	(block 
	  (script-comment "`force-substitution' at (0)")
	  direct-inference
	  (backchain-backwards "with(f:sets[nn],f=f);")
	  (apply-macete-with-minor-premises tr%domain-membership-iff-defined)))
      (block 
	(script-comment "`force-substitution' at (0)")
	direct-and-antecedent-inference-strategy
	(cut-with-single-formula "forall(p:nn, #(omega%embedding(dom{s})(p)) 
                     iff 
                   omega%embedding(dom{s})(p) in ran{omega%embedding(dom{s})})")
	(move-to-sibling 1)
	(block 
	  (script-comment "`cut-with-single-formula' at (1)")
	  (apply-macete-with-minor-premises tr%range-domain-membership)
	  (apply-macete-with-minor-premises indicator-facts-macete)
	  beta-reduce-repeatedly)
	(block 
	  (script-comment "`cut-with-single-formula' at (0)")
	  (incorporate-antecedent "with(f:sets[nn],n:nn,forall(p:nn,#(n) iff n in f));")
	  (apply-macete-with-minor-premises ran-of-omega%embedding)
	  (force-substitution "#(omega%embedding(dom{s})(p))"
			      "p<k"
			      (0))
	  (move-to-sibling 1)
	  simplify
	  (block 
	    (script-comment "`force-substitution' at (0)")
	    (apply-macete-with-minor-premises tr%domain-membership-iff-defined)
	    direct-and-antecedent-inference-strategy
	    (cut-with-single-formula "length{lambda(p:nn, s(omega%embedding(dom{s})(p)))}=k")
	    simplify
	    (block 
	      (script-comment "`cut-with-single-formula' at (1)")
	      (apply-macete-with-minor-premises iota-free-definition-of-length)
	      (incorporate-antecedent "with(i:ind_1,k:nn,forall(p:nn,p<k iff #(i)));")
	      (force-substitution "s(omega%embedding(dom{s})(p))"
				  "collapse{s}(p)"
				  (0))
	      simplify-insistently)))))

    )))

(def-theorem collapse-of-finite-is-finite-lemma
  "forall(s:[nn,ind_1], 
        forsome(m:nn, forall(k:nn, m<=k implies not(#(s(k)))))
          implies
        f_seq_q{collapse{s}})"
  (theory sequences)
  (usages transportable-macete)
  (proof
   (

   
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "length{collapse{s}}<=m")
    (apply-macete-with-minor-premises length-of-collapse-lemma)

    )))

(def-quasi-constructor constrict
  "lambda(f:[nn,ind_1],a:sets[ind_1], 
            collapse(lambda(n:nn, if(f(n) in a, f(n), ?ind_1))))"
  (language sequences)
  (fixed-theories h-o-real-arithmetic))

(def-theorem length-of-constrict-of-finite-sequence
  "forall(s:[nn,ind_1],a:sets[ind_1], 
             f_seq_q{s} 
               implies 
             length{constrict{s,a}}<=length{s})"
  (theory sequences)
  (usages transportable-macete)
  (proof
   (


    (apply-macete-with-minor-premises length-of-collapse-lemma)
    beta-reduce-repeatedly
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "not(#(s(k)))")
    simplify
    (block 
      (script-comment "node added by `cut-with-single-formula' at (1)")
      (apply-macete-with-minor-premises meaning-of-length-rev)
      simplify)
    )))

(def-theorem constrict-of-finite-sequence-is-finite-sequence
  "forall(s:[nn,ind_1],a:sets[ind_1], f_seq_q{s} implies f_seq_q{constrict{s,a}})"
  (theory sequences)
  (usages transportable-macete)
  (proof
   (


    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "length{constrict{s,a}}<=length{s}")
    (apply-macete-with-minor-premises length-of-constrict-of-finite-sequence)

    )))

(include-files 
 (files (imps theories/cardinality/omega-embedding-supplements)))

(def-theorem omega%embedding-id-condition
  "forall(s:sets[nn], omega%embedding(s)=id{s} iff (s=sort_to_indic{nn} or 
forsome(n:nn, s=omega(n))))"
  (theory h-o-real-arithmetic)
  (proof
   (
    direct-inference
    (case-split ("f_indic_q{s}"))
    (block 
     (script-comment "`case-split' at (1)")
     (apply-macete-with-minor-premises characterization-of-omega-embedding-for-finite-sets)
     (apply-macete-with-minor-premises tr%ran-of-id)
     (apply-macete-with-minor-premises tr%dom-of-id)
     simplify
     direct-and-antecedent-inference-strategy
     auto-instantiate-existential
     (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (1 0 0)")
      (contrapose "with(s:sets[nn],f_indic_q{s});")
      (apply-macete-with-minor-premises subset-of-nn-finite-iff-bounded)
      (contrapose "with(p:prop,not(p));")
      (antecedent-inference "with(p:prop,forsome(n:nn,p));")
      (contrapose "with(f,s:sets[nn],s subseteq f);")
      (unfold-single-defined-constant (0) omega)
      (apply-macete-with-minor-premises indicator-facts-macete)
      beta-reduce-repeatedly
      (backchain "with(f,s:sets[nn],s=f);")
      (instantiate-existential ("n+1"))
      simplify
      simplify)
     (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (1 0 1
0)")
      (backchain "with(f,s:sets[nn],s=f);")
      (backchain "with(f,s:sets[nn],s=f);")
      (apply-macete-with-minor-premises f-card-of-a-finite-cardinal))
     (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (1 1 0
0 0 0 0)")
      (backchain "with(s:sets[nn],s=sort_to_indic{nn});")
      (apply-macete-with-minor-premises tr%meaning-of-indic-from-sort-element))
     (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (1 1 0
0 0 0 1 0)")
      (backchain "with(n:nn,s:sets[nn],s=omega(n));")
      (incorporate-antecedent "with(l:nn,s:sets[nn],l in s);")
      (backchain "with(n:nn,s:sets[nn],s=omega(n));")
      (unfold-single-defined-constant-globally omega)
      (apply-macete-with-minor-premises indicator-facts-macete)
      beta-reduce-repeatedly
      simplify))
    (block 
     (script-comment "`case-split' at (2)")
     (apply-macete-with-minor-premises characterization-of-omega-embedding-for-infinite-sets)
     (apply-macete-with-minor-premises tr%ran-of-id)
     (apply-macete-with-minor-premises tr%dom-of-id)
     simplify
     direct-and-antecedent-inference-strategy
     (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (1 0 1 0)")
      (contrapose "with(p:prop,not(p));")
      (backchain "with(f,s:sets[nn],s=f);")
      (apply-macete-with-minor-premises finite-cardinal-is-f-indic))
     (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (1 1 0 0 0 0 0)")
      (backchain "with(f,s:sets[nn],s=f);")
      (apply-macete-with-minor-premises tr%meaning-of-indic-from-sort-element))
     (backchain "with(s:sets[nn],s=sort_to_indic{nn});")))))

(def-theorem collapse-invariance-condition
  "forall(s:[nn -> ind_1], (dom{s}=sort_to_indic{nn} or f_seq_q{s}) implies
                             collapse{s}=s)"
  (theory sequences)
  (proof
   (


    direct-and-antecedent-inference-strategy
    (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (0 0 0)")
      extensionality
      simplify
      (cut-with-single-formula "omega%embedding(dom{s})=id{dom{s}}")
      (move-to-sibling 1)
      (block 
	(script-comment "`cut-with-single-formula' at (1)")
	(apply-macete-with-minor-premises omega%embedding-id-condition)
	direct-and-antecedent-inference-strategy)
      (block 
	(script-comment "`cut-with-single-formula' at (0)")
	(backchain "with(f:[nn,nn],f=f);")
	simplify))
    (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (0 0 1)")
      extensionality
      simplify
      (cut-with-single-formula "omega%embedding(dom{s})=id{dom{s}}")
      (move-to-sibling 1)
      (block 
	(script-comment "`cut-with-single-formula' at (1)")
	(apply-macete-with-minor-premises omega%embedding-id-condition)
	direct-and-antecedent-inference-strategy
	(instantiate-existential ("length{s}"))
	(unfold-single-defined-constant (0) omega)
	(apply-macete-with-minor-premises meaning-of-length))
      (block 
	(script-comment "`cut-with-single-formula' at (0)")
	(backchain "with(f:[nn,nn],f=f);")
	simplify))


    )))
