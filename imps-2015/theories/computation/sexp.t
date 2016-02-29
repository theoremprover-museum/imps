(herald sexp)

(load-section sequences)

(def-language language-sexpression
  (embedded-language h-o-real-arithmetic)
  (base-types sexp)
  (constants 
   (nulle "sexp")
   (pair "[sexp, sexp -> sexp]")
   (car "[sexp -> sexp]")
   (cdr "[sexp -> sexp]")))
  

(def-theory sexpression
  (language language-sexpression)
  (component-theories h-o-real-arithmetic)
  (axioms
   (nulle-is-not-pair "forall(x,y:sexp, not (nulle = pair(x,y)))")
   (car-cdr-same-domain "dom{car}=dom{cdr}" rewrite)
   (pair-car-cdr "forall(x:sexp, x in dom{car} implies pair(car(x),cdr(x))=x)")
   (car-pair-rewrite "forall(x,y:sexp, car(pair(x,y)) = x)" rewrite)
   (cdr-pair-rewrite "forall(x,y:sexp, cdr(pair(x,y)) = y)" rewrite)))

(def-theorem cdr-nulle-undefined
  "not(#(cdr(nulle)))"
  (theory  sexpression)
  (proof
   (

    (cut-with-single-formula "forall(x,y:sexp, not (nulle = pair(x,y)))")
    (block 
     (script-comment "`cut-with-single-formula' at (0)")
     (contrapose "with(p:prop,p);")
     (cut-with-single-formula "#(car(nulle))")
     (move-to-sibling 1)
     (block 
      (script-comment "`cut-with-single-formula' at (1)")
      (apply-macete-with-minor-premises tr%rev%domain-membership-iff-defined)
      (apply-macete-with-minor-premises car-cdr-same-domain)
      simplify)
     (block 
      (script-comment "`cut-with-single-formula' at (0)")
      (instantiate-existential ("car(nulle)" "cdr(nulle)"))
      (apply-macete-with-minor-premises pair-car-cdr)))
    (apply-macete-with-minor-premises nulle-is-not-pair)

    )))

(include-files
 (files (imps theories/generic-theories/iterate-supplements)))

(def-translation ind_1-to-sexp
  (source generic-theory-1)
  (target sexpression)
  (fixed-theories h-o-real-arithmetic)
  (sort-pairs (ind_1 sexp))
  (theory-interpretation-check using-simplification))

(def-renamer ind_1-to-sexp-renamer
  (pairs
   (iterate sexp%iterate)))


(def-transported-symbols (iterate)
  (translation ind_1-to-sexp)
  (renamer ind_1-to-sexp-renamer))

(def-overloading iterate
  (generic-theory-1  iterate)
  (sexpression sexp%iterate))

(def-constant nth%cdr
  "lambda(n:nn, x:sexp, iterate(cdr,x)(n))"
  (theory sexpression))

(def-constant nth
  "lambda(n:nn, x:sexp, car(iterate(cdr,x)(n)))"
  (theory sexpression))

(def-atomic-sort sexp%list
  "lambda(f:[nn,sexp], f_seq_q{f})"
  (theory sexpression)
  (witness "lambda(x:nn, ?sexp)"))

(def-recursive-constant list
  "lambda(s:[sexp%list -> sexp], 
     lambda(f:sexp%list, if(f=nil{sexp}, nulle, pair(f(0), s(drop(f,1))))))"
  (theory sexpression))

(def-constant sexp%length
  "lambda(x:sexp, iota(n:nn, nth%cdr(n,x)=nulle))"
  (theory sexpression))

(def-constant p%list_q
  "lambda(x:sexp, #(sexp%length(x)))"
  (theory sexpression))

(def-theorem iterate-definedness-refinement
  "forall(f:[ind_1,ind_1],x:ind_1,z,j:zz, 
     0<=j and j<=z and #(iterate(f,x)(z)) implies #(iterate(f,x)(j)))"
  (usages transportable-macete)
  (theory generic-theory-1)
  (proof existing-theorem))

(def-theorem iota-free-characterization-of-sexp%length
  "forall(x:sexp, n:nn, sexp%length(x)=n iff nth%cdr(n,x)=nulle)"
  (theory sexpression)
  (proof
   (


    (unfold-single-defined-constant-globally sexp%length)
    (apply-macete-with-minor-premises eliminate-iota-macete)
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "not(b<n) and not(n<b)")
    simplify
    (block 
     (script-comment "`cut-with-single-formula' at (1)")
     direct-and-antecedent-inference-strategy
     (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (0)")
      (contrapose "with(x:sexp,n:nn,nth%cdr(n,x)=nulle);")
      (cut-with-single-formula "not(#(nth%cdr(n,x)))")
      simplify
      (block 
       (script-comment "`cut-with-single-formula' at (1)")
       (incorporate-antecedent "with(s:sexp,s=nulle);")
       (unfold-single-defined-constant-globally nth%cdr)
       direct-and-antecedent-inference-strategy
       (cut-with-single-formula "not(#(iterate(cdr,x)(b+1)))")
       (block 
	(script-comment "`cut-with-single-formula' at (0)")
	(contrapose "with(p:prop,not(p));")
	(apply-macete-with-minor-premises tr%iterate-definedness-refinement)
	auto-instantiate-existential
	simplify
	simplify)
       (block 
	(script-comment "`cut-with-single-formula' at (1)")
	(unfold-single-defined-constant-globally sexp%iterate)
	simplify
	(apply-macete-with-minor-premises cdr-nulle-undefined))))
     (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (1)")
      (weaken (0))
      (contrapose "with(x:sexp,b:nn,nth%cdr(b,x)=nulle);")
      (cut-with-single-formula "not(#(nth%cdr(b,x)))")
      simplify
      (block 
       (script-comment "`cut-with-single-formula' at (1)")
       (incorporate-antecedent "with(s:sexp,s=nulle);")
       (unfold-single-defined-constant-globally nth%cdr)
       direct-and-antecedent-inference-strategy
       (cut-with-single-formula "not(#(iterate(cdr,x)(n+1)))")
       (block 
	(script-comment "`cut-with-single-formula' at (0)")
	(contrapose "with(p:prop,not(p));")
	(apply-macete-with-minor-premises tr%iterate-definedness-refinement)
	auto-instantiate-existential
	simplify
	simplify)
       (block 
	(script-comment "`cut-with-single-formula' at (1)")
	(unfold-single-defined-constant (0) sexp%iterate)
	simplify
	(apply-macete-with-minor-premises cdr-nulle-undefined)))))
    )))

(def-constant sexp%to%seq
  "lambda(x:sexp, lambda(n:nn, nth(n,x)))"
  (theory sexpression))

(def-theorem car-iterate-defined-lemma
  "forall(x:sexp,i:nn, #(car(iterate(cdr,x)(i))) iff #(iterate(cdr,x)(i+1)))"
  (theory sexpression)
  lemma
  (proof
   (

    direct-and-antecedent-inference-strategy
    (block 
     (script-comment "`direct-and-antecedent-inference-strategy' at (0 0)")
     (unfold-single-defined-constant (0) sexp%iterate)
     simplify
     (apply-macete-with-minor-premises tr%rev%domain-membership-iff-defined)
     (cut-with-single-formula "dom{car}=dom{cdr}")
     (block 
      (script-comment "`cut-with-single-formula' at (0)")
      (backchain-backwards "with(f:sets[sexp],f=f);")
      (apply-macete-with-minor-premises tr%domain-membership-iff-defined))
     (apply-macete-with-minor-premises car-cdr-same-domain))
    (block 
     (script-comment "`direct-and-antecedent-inference-strategy' at (0 1)")
     (incorporate-antecedent "with(p:prop,p);")
     (unfold-single-defined-constant (0) sexp%iterate)
     simplify
     direct-and-antecedent-inference-strategy
     (apply-macete-with-minor-premises tr%rev%domain-membership-iff-defined)
     (apply-macete-with-minor-premises car-cdr-same-domain)
     (apply-macete-with-minor-premises tr%domain-membership-iff-defined))

    )))


(def-theorem sexp%seq-is-fseq-or-total
  "forall(x:sexp, f_seq_q{sexp%to%seq(x)} or total_q{sexp%to%seq(x),[nn,sexp]})"
  (theory sexpression)
  (proof
   (


    (unfold-single-defined-constant-globally sexp%to%seq)
    (unfold-single-defined-constant-globally nth)
    direct-and-antecedent-inference-strategy
    simplify-insistently
    (apply-macete-with-minor-premises car-iterate-defined-lemma)
    direct-and-antecedent-inference-strategy
    (contrapose "with(p:prop,p);")
    (apply-macete-with-minor-premises tr%f_seq_q-characterization)
    simplify
    (apply-macete-with-minor-premises car-iterate-defined-lemma)
    direct-and-antecedent-inference-strategy
    (block 
     (script-comment "`direct-and-antecedent-inference-strategy' at (0 0 0 0 0)")
     (apply-macete-with-minor-premises tr%iterate-definedness-refinement)
     auto-instantiate-existential
     simplify
     simplify)
    auto-instantiate-existential
    )))

(def-theorem sexp%to%seq-0-characterization-lemma
  "forall(x:sexp,not(sexp%to%seq(x)=nil{sexp}) implies sexp%to%seq(x)(0)=car(x))"
  (theory sexpression)
  (proof
   (

    (unfold-single-defined-constant-globally sexp%to%seq)
    (unfold-single-defined-constant-globally nth)
    (apply-macete-with-minor-premises tr%rev%length-0-iff-nil)
    (apply-macete-with-minor-premises tr%iota-free-definition-of-length)
    simplify
    (apply-macete-with-minor-premises car-iterate-defined-lemma)
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "iterate(cdr,x)(0)=x")
    (block 
     (script-comment "`cut-with-single-formula' at (0)")
     simplify
     (apply-macete-with-minor-premises tr%rev%domain-membership-iff-defined)
     (apply-macete-with-minor-premises car-cdr-same-domain)
     (apply-macete-with-minor-premises tr%domain-membership-iff-defined)
     (incorporate-antecedent "with(x,s:sexp,s=x);")
     (unfold-single-defined-constant-globally sexp%iterate)
     simplify
     (cut-with-single-formula "#(iterate(cdr,x)(1))")
     (block 
      (script-comment "`cut-with-single-formula' at (0)")
      (incorporate-antecedent "with(f:[zz,sexp],#(f(1)));")
      (unfold-single-defined-constant-globally sexp%iterate)
      simplify
      (unfold-single-defined-constant (0) sexp%iterate))
     (block 
      (script-comment "`cut-with-single-formula' at (1)")
      (apply-macete-with-minor-premises tr%iterate-definedness-refinement)
      simplify
      auto-instantiate-existential
      simplify))
    (unfold-single-defined-constant (0) sexp%iterate)

    )))

(def-theorem iterate-front-back-lemma
  iterate-front-back-lemma
  (theory generic-theory-1)
  lemma
  reverse
  (usages transportable-macete)
  (proof existing-theorem))

(def-theorem sexp%to%seq-drop-characterization-lemma
  "forall(x:sexp, not(sexp%to%seq(x)=nil{sexp}) implies drop{sexp%to%seq(x),1}=sexp%to%seq(cdr(x)))"
  (theory sexpression)
  (proof
   (

    (unfold-single-defined-constant-globally sexp%to%seq)
    (unfold-single-defined-constant-globally nth)
    (apply-macete-with-minor-premises tr%rev%length-0-iff-nil)
    (apply-macete-with-minor-premises tr%iota-free-definition-of-length)
    simplify
    direct-and-antecedent-inference-strategy
    extensionality
    (block 
     (script-comment "`extensionality' at (0)")
     simplify
     direct-and-antecedent-inference-strategy
     beta-reduce-repeatedly
     beta-reduce-with-minor-premises
     (move-to-sibling 1)
     (block 
      (script-comment "`beta-reduce-with-minor-premises' at (1)")
      (incorporate-antecedent "with(p:prop,p);")
      (apply-macete-with-minor-premises car-iterate-defined-lemma)
      direct-and-antecedent-inference-strategy
      (cut-with-single-formula "#(iterate(cdr,x)(1))")
      (block 
       (script-comment "`cut-with-single-formula' at (0)")
       (incorporate-antecedent "with(f:[zz,sexp],#(f(1)));")
       (unfold-single-defined-constant (0) sexp%iterate)
       simplify
       (unfold-single-defined-constant (0) sexp%iterate))
      (block 
       (script-comment "`cut-with-single-formula' at (1)")
       (apply-macete-with-minor-premises tr%iterate-definedness-refinement)
       simplify
       auto-instantiate-existential
       simplify))
     (block 
      (script-comment "`beta-reduce-with-minor-premises' at (0)")
      simplify
      (cut-with-single-formula "iterate(cdr,x)(1+x_0)==iterate(cdr,cdr(x))(x_0)")
      (apply-macete-with-minor-premises tr%rev%iterate-front-back-lemma)
      (unfold-single-defined-constant (0) sexp%iterate)
      simplify))
    simplify
    )))

(def-theorem pair-totality
  "forall(x,y:sexp ,#(pair(x,y)))"
  (theory sexpression)
  (usages d-r-convergence)
  (proof
   (

    insistent-direct-inference
    (cut-with-single-formula "car(pair(x,y))=x")
    (apply-macete-with-minor-premises car-pair-rewrite)

    )))

(def-theorem list-totality
  "forall(f:sexp%list, #(list(f)))"
  (theory sexpression)
  (usages d-r-convergence)
  (proof
   (


    insistent-direct-inference
    (cut-with-single-formula "forall(n:zz, 0<=n implies forall(x:sexp%list, length{x}=n implies #(list(x))))")
    (block 
     (script-comment "`cut-with-single-formula' at (0)")
     (backchain "with(p:prop,p);")
     (instantiate-existential ("length{f}"))
     (cut-with-single-formula "f_seq_q{f}")
     (apply-macete-with-minor-premises tr%length-non-negative)
     (apply-macete-with-minor-premises sexp%list-in-quasi-sort_sexpression))
    (block 
     (script-comment "`cut-with-single-formula' at (1)")
     (induction complete-inductor ("n"))
     (case-split ("m_$0=0"))
     (block 
      (script-comment "`case-split' at (1)")
      (incorporate-antecedent "with(m_$0:zz,x:sexp%list,length{x}=m_$0);")
      (backchain "with(m_$0:zz,m_$0=0);")
      (apply-macete-with-minor-premises tr%length-0-iff-nil)
      direct-and-antecedent-inference-strategy
      (backchain "with(f:[nn,sexp],x:sexp%list,x=f);")
      (unfold-single-defined-constant (0) list))
     (block 
      (script-comment "`case-split' at (2)")
      (unfold-single-defined-constant (0) list)
      (apply-macete-with-minor-premises tr%rev%length-0-iff-nil)
      simplify
      (apply-macete-with-minor-premises tr%sequence-defined-up-to-length)
      simplify
      (backchain "with(p:prop,forall(k:zz,p));")
      (block 
       (script-comment "`backchain' at (0)")
       (instantiate-existential ("m_$0-1"))
       simplify
       simplify
       (block 
	(script-comment "`instantiate-existential' at (0 1)")
	(apply-macete-with-minor-premises tr%length-of-drop)
	simplify))
      (block 
       (script-comment "`backchain' at (1)")
       (apply-macete-with-minor-premises sexp%list-defining-axiom_sexpression)
       simplify)))

    )))


(def-theorem nth%cdr-list
  "forall(f:sexp%list,nth%cdr(length{f},list(f))=nulle)"
  (theory sexpression)
  (proof
   (


    (cut-with-single-formula "forall(n:zz, 0<=n implies forall(f:sexp%list , length{f}=n implies nth%cdr(n,list(f))=nulle))")
    (block 
     (script-comment "`cut-with-single-formula' at (0)")
     direct-and-antecedent-inference-strategy
     (instantiate-universal-antecedent "with(p:prop,p);" ("length{f}"))
     (block 
      (script-comment "`instantiate-universal-antecedent' at (0 0 0)")
      (contrapose "with(p:prop,p);")
      (apply-macete-with-minor-premises tr%length-non-negative)
      (apply-macete-with-minor-premises sexp%list-in-quasi-sort_sexpression))
     (block 
      (script-comment "`instantiate-universal-antecedent' at (0 0 1)")
      (backchain "with(p:prop,p);")
      simplify
      (apply-macete-with-minor-premises sexp%list-in-quasi-sort_sexpression))
     (apply-macete-with-minor-premises sexp%list-in-quasi-sort_sexpression))
    (block 
     (script-comment "`cut-with-single-formula' at (1)")
     (induction complete-inductor ("n"))
     (case-split ("m_$0=0"))
     (block 
      (script-comment "`case-split' at (1)")
      (incorporate-antecedent "with(m_$0:zz,f:sexp%list,length{f}=m_$0);")
      simplify
      (unfold-single-defined-constant (0) nth%cdr)
      (unfold-single-defined-constant (0) sexp%iterate)
      simplify
      (unfold-single-defined-constant (0) list)
      simplify)
     (block 
      (script-comment "`case-split' at (2)")
      (unfold-single-defined-constant (0) nth%cdr)
      (instantiate-universal-antecedent "with(p:prop,forall(k:zz,p));"
					("m_$0-1"))
      (simplify-antecedent "with(r:rr,not(0<=r));")
      (simplify-antecedent "with(m_$0:zz,r:rr,not(r<m_$0));")
      (block 
       (script-comment "`instantiate-universal-antecedent' at (0 0 1)")
       (instantiate-universal-antecedent "with(p:prop,forall(f_$0:sexp%list,p));"
					 ("drop{f,1}"))
       (block 
	(script-comment "`instantiate-universal-antecedent' at (0 0 0)")
	(contrapose "with(m_$0:zz,f:[nn,sexp],not(length{f}=m_$0-1));")
	(apply-macete-with-minor-premises tr%length-of-drop)
	simplify)
       (block 
	(script-comment "`instantiate-universal-antecedent' at (0 0 1)")
	(incorporate-antecedent "with(s:sexp,s=nulle);")
	(unfold-single-defined-constant (0) nth%cdr)
	(unfold-single-defined-constant (1) sexp%iterate)
	simplify
	(unfold-single-defined-constant (1) list)
	simplify
	(cut-with-single-formula "not(f = nil{sexp})")
	(block 
	 (script-comment "`cut-with-single-formula' at (0)")
	 simplify
	 (apply-macete-with-minor-premises tr%iterate-front-back-lemma)
	 (apply-macete-with-minor-premises cdr-pair-rewrite)
	 (apply-macete-with-minor-premises tr%sequence-defined-up-to-length)
	 simplify)
	(block 
	 (script-comment "`cut-with-single-formula' at (1)")
	 (apply-macete-with-minor-premises tr%rev%length-0-iff-nil)
	 simplify))
       (block 
	(script-comment "`instantiate-universal-antecedent' at (1 1 0 0 (1 . 0))")
	(apply-macete-with-minor-premises sexp%list-defining-axiom_sexpression)
	simplify
	(apply-macete-with-minor-premises sexp%list-in-quasi-sort_sexpression)
	simplify
	(apply-macete-with-minor-premises tr%drop-is-fseq)))))


    )))


(def-theorem sexp%length-of-list
  "forall(x:sexp,f:sexp%list,
     x=list(f) implies #(sexp%length(x)))"
  (theory sexpression)
  (proof
   (

    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "forsome(n:nn, sexp%length(x)=n)")
    (antecedent-inference "with(p:prop,forsome(n:nn,p));")
    (block 
     (script-comment "`cut-with-single-formula' at (1)")
     (apply-macete-with-minor-premises iota-free-characterization-of-sexp%length)
     (backchain "with(p:prop,p);")
     (instantiate-existential ("length{f}"))
     (apply-macete-with-minor-premises nth%cdr-list)
     (apply-macete-with-minor-premises sexp%list-in-quasi-sort_sexpression))
    )))

(def-theorem list-characterization
  "forall(x:sexp, p%list_q(x) iff x=list(sexp%to%seq(x)))"
  (theory sexpression)
  (proof
   (

    (unfold-single-defined-constant-globally p%list_q)
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "forsome(n:nn, sexp%length(x)=n)")
    (antecedent-inference "with(p:prop,forsome(n:nn,p));")
    (incorporate-antecedent "with(n:nn,n=n);")
    (apply-macete-with-minor-premises iota-free-characterization-of-sexp%length)
    (weaken (0))
    (cut-with-single-formula "forall(n:zz, 0<=n implies forall(x:sexp, nth%cdr(n,x)=nulle implies x=list(sexp%to%seq(x))))")
    simplify
    (induction complete-inductor ("n"))
    (unfold-single-defined-constant (0) list)
    beta-reduce-with-minor-premises
    (move-to-sibling 1)
    (block 
     (script-comment "`beta-reduce-with-minor-premises' at (1)")
     (apply-macete-with-minor-premises sexp%list-defining-axiom_sexpression)
     beta-reduce-with-minor-premises
     (move-to-sibling 1)
     (unfold-single-defined-constant (0) sexp%to%seq)
     (block 
      (script-comment "`beta-reduce-with-minor-premises' at (0)")
      (cut-with-single-formula "forall(x:sexp, f_seq_q{sexp%to%seq(x)} or total_q{sexp%to%seq(x),[nn,sexp]})")
      (block 
       (script-comment "`cut-with-single-formula' at (0)")
       (instantiate-universal-antecedent "with(p:prop,forall(x:sexp,p));"
					 ("x"))
       (contrapose "with(f:[nn,sexp],total_q{f,[nn,sexp]});")
       (incorporate-antecedent "with(s:sexp,s=nulle);")
       (unfold-single-defined-constant-globally nth%cdr)
       (unfold-single-defined-constant-globally sexp%to%seq)
       (unfold-single-defined-constant-globally nth)
       direct-and-antecedent-inference-strategy
       (instantiate-existential ("m"))
       (backchain "with(s:sexp,s=nulle);")
       (apply-macete-with-minor-premises tr%rev%domain-membership-iff-defined)
       (apply-macete-with-minor-premises car-cdr-same-domain)
       (apply-macete-with-minor-premises tr%domain-membership-iff-defined)
       (apply-macete-with-minor-premises cdr-nulle-undefined))
      (apply-macete-with-minor-premises sexp%seq-is-fseq-or-total)))
    (case-split ("sexp%to%seq(x)=nil{sexp}"))
    (block 
     (script-comment "`case-split' at (1)")
     simplify
     (incorporate-antecedent "with(f:[nn,sexp],f=f);")
     (unfold-single-defined-constant (0) sexp%to%seq)
     (unfold-single-defined-constant (0) nth)
     (apply-macete-with-minor-premises tr%rev%length-0-iff-nil)
     (apply-macete-with-minor-premises tr%iota-free-definition-of-length)
     simplify
     (apply-macete-with-minor-premises car-iterate-defined-lemma)
     (incorporate-antecedent "with(s:sexp,s=nulle);")
     (unfold-single-defined-constant-globally nth%cdr)
     direct-and-antecedent-inference-strategy
     (case-split ("m=0"))
     (block 
      (script-comment "`case-split' at (1)")
      (contrapose "with(s:sexp,s=nulle);")
      simplify
      (unfold-single-defined-constant (0) sexp%iterate))
     (block 
      (script-comment "`case-split' at (2)")
      (contrapose "with(p:prop,forall(m_$0:nn,not(p)));")
      (instantiate-existential ("m-1"))
      simplify))
    simplify
    (cut-with-single-formula "sexp%to%seq(x)(0)=car(x) and list(drop{sexp%to%seq(x),1})=cdr(x)")
    (block 
     (script-comment "`cut-with-single-formula' at (0)")
     (backchain "with(p:prop,p and p);")
     (backchain "with(p:prop,p and p);")
     (apply-macete-with-minor-premises pair-car-cdr))
    direct-and-antecedent-inference-strategy
    (instantiate-theorem sexp%to%seq-0-characterization-lemma ("x"))
    (instantiate-theorem sexp%to%seq-drop-characterization-lemma ("x"))
    (backchain "with(f:[nn,sexp],f=f);")
    (instantiate-universal-antecedent "with(p:prop,forall(k:zz,p));" ("m-1"))
    (block 
     (script-comment "`instantiate-universal-antecedent' at (0 0 0 0)")
     (simplify-antecedent "with(r:rr,not(0<=r));")
     (cut-with-single-formula "m=0")
     (move-to-sibling 1)
     simplify
     (block 
      (script-comment "`cut-with-single-formula' at (0)")
      (incorporate-antecedent "with(s:sexp,s=nulle);")
      (unfold-single-defined-constant (0) nth%cdr)
      (unfold-single-defined-constant (0) sexp%iterate)
      simplify
      direct-and-antecedent-inference-strategy
      (contrapose "with(f:[nn,sexp],not(f=f));")
      (unfold-single-defined-constant (0) sexp%to%seq)
      (unfold-single-defined-constant (0) nth)
      simplify
      (apply-macete-with-minor-premises tr%rev%length-0-iff-nil)
      (apply-macete-with-minor-premises tr%iota-free-definition-of-length)
      simplify
      direct-and-antecedent-inference-strategy
      (apply-macete-with-minor-premises car-iterate-defined-lemma)
      (unfold-single-defined-constant (0) sexp%iterate)
      simplify
      (apply-macete-with-minor-premises tr%iterate-front-back-lemma)
      (cut-with-single-formula "not(#(cdr(nulle)))")
      (apply-macete-with-minor-premises cdr-nulle-undefined)))
    (simplify-antecedent "with(m:zz,r:rr,not(r<m));")
    (instantiate-universal-antecedent "with(p:prop,forall(x_$0:sexp,p));"
				      ("cdr(x)"))
    (contrapose "with(s:sexp,not(s=nulle));")
    (incorporate-antecedent "with(s:sexp,s=nulle);")
    (unfold-single-defined-constant-globally nth%cdr)
    simplify
    (move-to-ancestor 1)
    beta-reduce-with-minor-premises
    (move-to-ancestor 4)
    (block 
     (script-comment "`contrapose' at (0)")
     (case-split ("m=0"))
     (incorporate-antecedent "with(s:sexp,s=nulle);")
     (unfold-single-defined-constant-globally nth%cdr)
     (apply-macete-with-minor-premises tr%rev%iterate-front-back-lemma)
     (unfold-single-defined-constant (0) sexp%iterate)
     simplify)
    (instantiate-existential ("sexp%length(x)"))
    (block 
     (script-comment "`direct-and-antecedent-inference-strategy' at (0 1)")
     (apply-macete-with-minor-premises sexp%length-of-list)
     auto-instantiate-existential)

    )))