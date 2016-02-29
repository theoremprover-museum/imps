(include-files (files (imps theories/vmach/machines)))


(def-theorem copy-definedness
  "forall(phi:[place -> word], h:[place -> place], #(copy(phi,h)))"
  (theory places)
  (usages d-r-convergence)
  (proof
   (
    (unfold-single-defined-constant-globally copy)
    simplify-insistently)))

(def-theorem a%copy-definedness
  "forall(phi:[place -> word], h:[place -> place], copy%fn(phi,h) implies #(a%copy(phi,h)))"
  (theory places)
  (usages d-r-convergence)
  (proof
   (
    (unfold-single-defined-constant-globally a%copy)
    simplify)))

(def-theorem user%eq-transitivity
  "forall(gamma_0, gamma_1, gamma_2:[place -> word], v:sets[place], 
    user%eq(gamma_0,gamma_1, v)  and user%eq(gamma_1,gamma_2, v)
    implies user%eq(gamma_0,gamma_2, v))"
  (theory places)
  (proof
   (
    (unfold-single-defined-constant-globally user%eq)
    direct-and-antecedent-inference-strategy)))

(def-theorem user%eq-abstr
  "forall (sigma_1, sigma_2:istate, v:sets[place], 
    user%eq(abstr(sigma_1), abstr(sigma_2), v) 
    iff
     restrict{lambda(p:place, promote(sigma_1, p)),v}
    =restrict{lambda(p:place, promote(sigma_2, p)),v})"
  (theory places)
  (proof
   (
    (unfold-single-defined-constant-globally abstr)
    (unfold-single-defined-constant-globally user%eq))))


(def-theorem c%shadow-definedness
  "forall(sigma:istate, f:[place -> place], copy%fn(abstr(sigma),f) implies 
	#(c%shadow(sigma, f)))"
  (theory places)
  (usages d-r-convergence)
  (proof
   (
    (unfold-single-defined-constant-globally c%shadow)
    simplify
    (apply-macete-with-minor-premises copy-liveness-corollary)
    simplify)))

(def-theorem lower-definedness
  "forall(sigma:istate, h:[place -> place], 
	#(lower(sigma,h)))"
  (theory places)
  (usages d-r-convergence)
  (proof
   (
    (unfold-single-defined-constant-globally lower)
    simplify-insistently)))

(def-theorem c%copy-definedness
  "forall(sigma:istate, h:[place -> place], 
     copy%fn(abstr(sigma),h) implies
       #(c%copy(sigma,lower(sigma,h))))"
  (theory places)
  (proof
   (
    (apply-macete-with-minor-premises copy-liveness-corollary)
    simplify)))

(def-theorem lower-is-c%copy%fn
   "forall(sigma:istate,h:[place,place],p:place,
	c%copy%fn(sigma,lower(sigma,h)))"
   (theory places)
   (proof
    (
     (unfold-single-defined-constant-globally c%copy%fn)
     (unfold-single-defined-constant-globally lower)
     simplify)))

(def-theorem default-c%copy-bound%place 
  "forall(sigma:istate, h:[place -> place], p:place, 
     p in bound%place(sigma) implies
       default(c%copy(sigma,lower(sigma,h)))(p)==default(sigma)(p))"
  (theory places)
  (proof
   (
    (unfold-single-defined-constant-globally c%copy)
    (apply-macete-with-minor-premises lower-is-c%copy%fn)
    simplify
    (unfold-single-defined-constant-globally lower)
    simplify)))

(def-theorem default-c%copy-un-bound%place
  "forall(sigma:istate, h:[place -> place], p:place, 
     not(p in bound%place(sigma)) implies
       default(c%copy(sigma,lower(sigma,h)))(p)==h(p))"
  (theory places)
  (proof
   (
    (unfold-single-defined-constant-globally c%copy)
    (apply-macete-with-minor-premises lower-is-c%copy%fn)
    simplify
    (unfold-single-defined-constant-globally lower)
    simplify)))


(def-theorem gamma-c%copy-unchanged
  "forall(sigma:istate, h:[place -> place], 
    gamma(c%copy(sigma,lower(sigma,h)))=gamma(sigma))"
  (theory places)
  (usages rewrite)
  (proof
   (
    (unfold-single-defined-constant-globally c%copy)
    (apply-macete-with-minor-premises lower-is-c%copy%fn)
    simplify)))

(def-theorem gamma-c%shadow-unchanged
  "forall(sigma:istate, f:[place -> place], 
  #(c%shadow(sigma,f)) implies 
   dom{gamma(c%shadow(sigma,f))}=dom{gamma(sigma)})"
  (theory places)
  (proof
   (
    (unfold-single-defined-constant-globally c%shadow)
    simplify)))


(def-theorem in-range-condition
  "forall(y:ind_1,h:[ind_1 -> ind_2], h(y) in ran{h} iff #(h(y)))"
  (theory generic-theory-2)
  (usages transportable-macete transportable-rewrite)
  (proof
   (
    direct-and-antecedent-inference-strategy
    beta-reduce-insistently
    simplify
    (instantiate-existential ("y_$0")))))



(def-theorem dom-ran-disjointness-lemma
  "forall(h,g:[ind_1->ind_1], dom{h} disj dom{g} implies
  dom{(inverse{g}) oo h} disj ran{(inverse{g}) oo h})"
  (theory generic-theory-1)
  (proof
   (
    simplify-insistently
    direct-and-antecedent-inference-strategy
    (case-split ("#(h(x_$5))"))
    (move-to-sibling 2)
    simplify
    (block 
      (script-comment "`case-split' at (1)")
      beta-reduce
      (eliminate-iota 0)
      direct-and-antecedent-inference-strategy
      auto-instantiate-existential
      (contrapose "with(p:prop,forall(x_$0:ind_1,p or p));")
      (instantiate-existential ("x_$0"))
      simplify))))


(def-theorem c%shadow-of-c%copy-definedness
  "forall(sigma:istate,g,h,f,h%plus:[place,place],v:sets[place],
  h%plus
  =lambda(p:place,if(p in bound%place(sigma), p, h(p)))
   and 
  copy%fn(abstr(sigma),h%plus)
   and 
  ran{h} subseteq bound%place(sigma)
   and 
  dom{h} disj bound%place(sigma)
   and 
  ran{h} disj ran{default(sigma)}
   and 
  bijective_on_q{g,dom{g},ran{h}}
   and 
  dom{g} disj bound%place(sigma)
   and 
  dom{g} disj dom{h}
   and 
  dom{g} disj ran{h}
   and 
  dom{g} disj v
   and 
  f
  =lambda(p:place,
     if(p in bound%place(c%copy(sigma,lower(sigma,h%plus))),
       p,
       #(g(p)),
       g(p),
       ?place))
   implies 
  #(c%shadow(c%copy(sigma,lower(sigma,h%plus)),f)));"
  (theory places)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (unfold-single-defined-constant-globally c%shadow)
    beta-reduce-with-minor-premises
    (move-to-sibling 1)
    (apply-macete-with-minor-premises c%copy-definedness)
    (block 
      (script-comment "`beta-reduce-with-minor-premises' at (0)")
      (raise-conditional (0))
      direct-inference
      (apply-macete-with-minor-premises copy-liveness-corollary)
      (block 
	(script-comment "`direct-inference' at (1)")
	(contrapose "with(p:prop,not(p));")
	(apply-macete-with-minor-premises a%copy-definedness)
	(unfold-single-defined-constant-globally copy%fn)
	direct-inference
	(block 
	  (script-comment "`direct-inference' at (0)")
	  (apply-macete-with-minor-premises tr%domain-membership-iff-defined)
	  (apply-macete-with-minor-premises rev%bound%place-abstr-definedness)
	  (backchain "with(f:[place,place],f)
=with(f:sets[place],
   lambda(p:place,
     with(p:prop,
       if(with(p:place,p in f),
         with(p:place,p),
         with(p:prop,p),
         with(p:place,p),
         with(p:place,p)))));")
	  beta-reduce
	  simplify)
	(block 
	  (script-comment "`direct-inference' at (1)")
	  (backchain "with(f:[place,place],f)
=with(f:sets[place],
   lambda(p:place,
     with(p:prop,
       if(with(p:place,p in f),
         with(p:place,p),
         with(p:prop,p),
         with(p:place,p),
         with(p:place,p)))));")
	  beta-reduce-insistently
	  (raise-conditional (0))
	  (raise-conditional (2))
	  direct-and-antecedent-inference-strategy
	  (contrapose "with(w:word,not(#(w)));")
	  (apply-macete-with-minor-premises rev%bound%place-abstr-definedness)
	  (backchain "with(p,x_$0:place,x_$0=p);")
	  (raise-conditional (0))
	  (raise-conditional (0))
	  simplify
	  direct-and-antecedent-inference-strategy
	  (block 
	    (script-comment "`direct-and-antecedent-inference-strategy' at (0 0)")
	    (contrapose "with(p,x_$0:place,x_$0=p);")
	    (raise-conditional (0))
	    (raise-conditional (0))
	    simplify)
	  (block 
	    (script-comment "`direct-and-antecedent-inference-strategy' at (0 1)")
	    (cut-with-single-formula "forsome(y:place, g(x)=h(y))")
	    (block 
	      (script-comment "`cut-with-single-formula' at (0)")
	      (antecedent-inference-strategy (0))
	      (backchain "with(y:place,h:[place,place],x:place,g:[place,place],
  g(x)=h(y));")
	      (apply-macete-with-minor-premises bound%place-abstr-definedness)
	      (apply-macete-with-minor-premises copy-liveness)
	      (unfold-single-defined-constant-globally a%copy)
	      (raise-conditional (0))
	      direct-and-antecedent-inference-strategy
	      (unfold-single-defined-constant-globally copy)
	      (backchain "with(h:[place,place],f:sets[place],h%plus:[place,place],
  h%plus=lambda(p:place,if(p in f, p, h(p))));")
	      beta-reduce
	      (raise-conditional (0))
	      (apply-macete-with-minor-premises rev%bound%place-abstr-definedness)
	      direct-and-antecedent-inference-strategy
	      (contrapose "with(y:place,h:[place,place],sigma:istate,
  not(h(y) in bound%place(sigma)));")
	      (backchain "with(f:sets[place],f subseteq f);")
	      (apply-macete-with-minor-premises tr%in-range-condition))
	    (block 
	      (script-comment "`cut-with-single-formula' at (1)")
	      (contrapose "with(h,g:[place,place],ran{g}=ran{h});")
	      extensionality
	      simplify-insistently
	      (instantiate-existential ("g(x)"))
	      (contrapose "with(x:place,g:[place,place],
  forall(x_$1:place,not(g(x)=g(x_$1))));")
	      (instantiate-existential ("x"))))))))))


(def-theorem default-in-bound-place-implies-bound
  "forall(p:place,sigma:istate,
     default(sigma)(p) in bound%place(sigma)
      implies 
     p in bound%place(sigma));"
  (theory places)
  (proof
   (
    (apply-macete-with-minor-premises bound%place-characterization)
    (apply-macete-with-minor-premises tr%meaning-of-indic-from-pred-element)
    simplify
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises tr%first%entry-equation)
    simplify)))


(def-theorem copy-fn-dom-bound
  "forall(h:[place,place],sigma:istate,
  #(c%copy(sigma,h)) and ran{h} subseteq bound%place(sigma)
   implies 
  dom{h} subseteq bound%place(c%copy(sigma,h)));"
  (theory places)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "default(c%copy(sigma,h))= h")
    (move-to-sibling 1)
    (block 
      (script-comment "`cut-with-single-formula' at (1)")
      (incorporate-antecedent "with(f:istate,#(f));")
      (unfold-single-defined-constant-globally c%copy)
      simplify)
    (block 
      (script-comment "`cut-with-single-formula' at (0)")
      simplify-insistently
      direct-and-antecedent-inference-strategy
      (apply-macete-with-minor-premises default-in-bound-place-implies-bound)
      simplify
      (instantiate-universal-antecedent "with(f:sets[place],f subseteq f);"
					("h(x_$0)"))
      (block 
	(script-comment "`instantiate-universal-antecedent' at (0 0 0)")
	(contrapose "with(p:prop,not(p));")
	(apply-macete-with-minor-premises tr%in-range-condition))
      (block 
	(script-comment "`instantiate-universal-antecedent' at (0 0 1)")
	(apply-macete-with-minor-premises bound%place%stability)
	direct-and-antecedent-inference-strategy)))))







(def-theorem c%shadow-c%copy-definedness
  "
    forall(sigma:istate,g,h,f,h%plus:[place,place],
      h%plus
      =lambda(p:place,if(p in bound%place(sigma), p, h(p)))
       and 
      copy%fn(abstr(sigma),h%plus)
       and 
      ran{h} subseteq bound%place(sigma)
       and
      ran{g}=ran{h}
       and 
      f
      =lambda(p:place,
         if(p in bound%place(c%copy(sigma,lower(sigma,h%plus))),
           p,
           #(g(p)),
           g(p),
           ?place))
       implies 
      #(c%shadow(c%copy(sigma,lower(sigma,h%plus)),f)))"
  (theory places)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises c%shadow-definedness)
    (unfold-single-defined-constant-globally copy%fn)
    beta-reduce-with-minor-premises
    (move-to-sibling 1)
    (apply-macete-with-minor-premises c%copy-definedness)
    (block 
      (script-comment "`beta-reduce-with-minor-premises' at (0)")
      (force-substitution "dom{abstr(c%copy(sigma,lower(sigma,h%plus)))}"
			  "bound%place(c%copy(sigma,lower(sigma,h%plus)))"
			  (0 1))
      (move-to-sibling 1)
      (block 
	(script-comment "`force-substitution' at (1)")
	extensionality
	simplify
	(apply-macete-with-minor-premises bound%place-abstr-definedness)
	direct-and-antecedent-inference-strategy
	(apply-macete-with-minor-premises tr%value-of-a-defined-indicator-application)
	(apply-macete-with-minor-premises bound%place-abstr-definedness))
      (block 
	(script-comment "`force-substitution' at (0)")
	(backchain-repeatedly ("with(g,h%plus:[place,place],sigma:istate,f:[place,place],
  f
  =lambda(p:place,
     if(p in bound%place(c%copy(sigma,lower(sigma,h%plus))),
       p,
       #(g(p)),
       g(p),
       ?place)));"))
	beta-reduce
	direct-and-antecedent-inference-strategy
	simplify
	(block 
	  (script-comment "`direct-and-antecedent-inference-strategy' at (1)")
	  beta-reduce-insistently
	  (apply-macete-with-minor-premises tr%definedness-of-dangling-conditionals)
	  direct-and-antecedent-inference-strategy
	  (incorporate-antecedent "with(p,x_$0:place,x_$0=p);")
	  (case-split-on-conditionals (0))
	  direct-inference
	  (cut-with-single-formula "forsome(y:place, x_$0=h(y))")
	  (block 
	    (script-comment "`cut-with-single-formula' at (0)")
	    (antecedent-inference "with(p:prop,forsome(y:place,p));")
	    (backchain "with(p,x_$0:place,x_$0=p);")
	    (instantiate-universal-antecedent "with(f:sets[place],f subseteq f);"
					      ("h(y)"))
	    (block 
	      (script-comment "`instantiate-universal-antecedent' at (0 0 0)")
	      (contrapose "with(y:place,h:[place,place],not(h(y) in ran{h}));")
	      (apply-macete-with-minor-premises tr%in-range-condition))
	    (block 
	      (script-comment "`instantiate-universal-antecedent' at (0 0 1)")
	      (apply-macete-with-minor-premises bound%place%stability)
	      (apply-macete-with-minor-premises c%copy-definedness)
	      direct-and-antecedent-inference-strategy))
	  (block 
	    (script-comment "`cut-with-single-formula' at (1)")
	    (contrapose "with(f:sets[place],f=f);")
	    extensionality
	    beta-reduce-insistently
	    simplify
	    (instantiate-existential ("g(x)"))
	    simplify
	    (block 
	      (script-comment "`instantiate-existential' at (0 1)")
	      (contrapose "with(p:prop,not(forsome(x_$0:place,p)));")
	      (instantiate-existential ("x"))))))))))





(def-theorem c%shadow-default
  "forall(sigma:istate, f:[place->place], 
    #(c%shadow(sigma,f)) implies default(c%shadow(sigma,f))=lower(sigma,f))"
  (theory places)
  (proof
   (
    (unfold-single-defined-constant-globally c%shadow)
    direct-inference
    (case-split-on-conditionals (0))
    (unfold-single-defined-constant-globally c%copy)
    (case-split-on-conditionals (0)))))

(def-theorem c%redirect-c%shadow-c%copy-defined
  "forall(sigma:istate, g, h, f, h%plus:[place -> place], v:sets[place],
    h%plus=lambda (p:place, if(p in bound%place(sigma), p, h(p)))
    and 
    copy%fn(abstr(sigma), h%plus)
    and 
    ran(h) subseteq bound%place(sigma)
    and 
    dom(h) disj bound%place(sigma)
    and 
    ran(h) disj ran(default(sigma)) 
    and 
    bijective_on_q{g,dom{g},ran{h}} 
    and
    dom(g) disj bound%place(sigma)
    and 
    dom(g) disj dom(h)
    and
    dom(g) disj ran(h)
    and 
    dom(g) disj v
    and 
    f=lambda(p:place, if(p in bound%place(c%copy(sigma,lower(sigma,h%plus))), p, #(g(p)), g(p),  ?place))
    implies 
    #(c%redirect(c%shadow(c%copy(sigma,lower(sigma,h%plus)),f),
                 (inverse{g}) oo h)))"
  (theory places)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (unfold-single-defined-constant-globally c%redirect)
    beta-reduce-with-minor-premises
    (raise-conditional (0))
    direct-inference
    simplify
    (block 
      (script-comment "`direct-inference' at (1)")
      (contrapose "with(p:prop,not(p));")
      (unfold-single-defined-constant-globally c%redirect%fn)
      beta-reduce-with-minor-premises
      (apply-macete-with-minor-premises gamma-c%shadow-unchanged)
      (apply-macete-with-minor-premises gamma-c%copy-unchanged)
      (apply-macete-with-minor-premises tr%range-composition)
      (apply-macete-with-minor-premises tr%ran-of-inverse)
      (move-to-sibling 2)
      (apply-macete-with-minor-premises tr%injective-iff-injective-on-domain)
      (move-to-sibling 1)
      (apply-macete-with-minor-premises tr%injective-iff-injective-on-domain)
      (block 
	(script-comment "`apply-macete-with-minor-premises' at (0)")
	(apply-macete-with-minor-premises tr%domain-composition)
	direct-and-antecedent-inference-strategy
	(block 
	  (script-comment "`direct-and-antecedent-inference-strategy' at (0)")
	  extensionality
	  simplify
	  (instantiate-universal-antecedent "with(sigma:istate,g:[place,place],
  dom{g} disj bound%place(sigma));"
					    ("x_0"))
	  (block 
	    (script-comment "`instantiate-universal-antecedent' at (0 0 0 0)")
	    (apply-macete-with-minor-premises tr%rev%domain-membership-iff-defined)
	    direct-inference)
	  (block 
	    (script-comment "`instantiate-universal-antecedent' at (0 0 0 1)")
	    direct-inference
	    (contrapose "with(x_0:place,f:sets[place],not(x_0 in f));")
	    (apply-macete-with-minor-premises bound%place-characterization)
	    (apply-macete-with-minor-premises tr%first%entry-identity-in-set)
	    (move-to-ancestor 1)
	    beta-reduce-insistently
	    (apply-macete-with-minor-premises tr%first%entry-identity-in-set)))
	(block 
	  (script-comment "`direct-and-antecedent-inference-strategy' at (1)")
	  extensionality
	  beta-reduce-insistently
	  (raise-conditional (0 1 2))
	  (move-to-ancestor 1)
	  simplify
	  (instantiate-universal-antecedent "with(h,g:[place,place],dom{g} disj dom{h});"
					    ("x_0"))
	  (move-to-ancestor 1)
	  (apply-macete-with-minor-premises tr%rev%domain-membership-iff-defined)
	  direct-inference
	  (backchain "with(p:prop,p or p);"))
	(move-to-ancestor 4)
	(move-to-descendent (2))
	(block 
	  (script-comment "`apply-macete-with-minor-premises' at (1 0)")
	  (apply-macete-with-minor-premises tr%dom-of-inverse)
	  (backchain "with(h,g:[place,place],ran{g}=ran{h});"))
	(move-to-ancestor 4)
	(move-to-descendent (1))
	(weaken (1))
	(move-to-ancestor 6)
	(move-to-descendent (2))
	(block 
	  (script-comment "`apply-macete-with-minor-premises' at (1 0)")
	  (apply-macete-with-minor-premises tr%dom-of-inverse)
	  (backchain "with(h,g:[place,place],ran{g}=ran{h});"))
	(move-to-ancestor 6)
	(move-to-descendent (1))
	(weaken (0 1))
	(move-to-ancestor 8)
	(move-to-descendent (1))
	(block 
	  (script-comment "`apply-macete-with-minor-premises' at (1)")
	  (apply-macete-with-minor-premises c%shadow-c%copy-definedness)
	  auto-instantiate-existential)
	(move-to-ancestor 8)
	(move-to-descendent (2))
	(apply-macete-with-minor-premises c%copy-definedness)
	(move-to-ancestor 9)
	(move-to-descendent (1))
	(block 
	  (script-comment "`beta-reduce-with-minor-premises' at (1)")
	  (apply-macete-with-minor-premises c%shadow-c%copy-definedness)
	  auto-instantiate-existential)
	(move-to-ancestor 14)
	(move-to-descendent (1))
	(block 
	  (script-comment "`beta-reduce-with-minor-premises' at (1)")
	  (apply-macete-with-minor-premises c%shadow-c%copy-definedness)
	  auto-instantiate-existential)
	(block 
	  (script-comment "`direct-and-antecedent-inference-strategy' at (2 0 0)")
	  beta-reduce-insistently
	  simplify-insistently
	  beta-reduce-with-minor-premises
	  (move-to-sibling 1)
	  (apply-macete-with-minor-premises tr%rev%domain-membership-iff-defined)
	  (block 
	    (script-comment "`beta-reduce-with-minor-premises' at (0)")
	    (cut-with-single-formula "#(h(x_$3))")
	    (cut-with-single-formula "#(iota(y:place,g(y)=h(x_$3)))")
	    (move-to-sibling 1)
	    (block 
	      (script-comment "`cut-with-single-formula' at (1)")
	      (eliminate-iota 0)
	      (contrapose "with(h,g:[place,place],ran{g}=ran{h});")
	      extensionality
	      beta-reduce-insistently
	      (weaken (17 16 15 14 13 12 11 10 9 8 6 3 2 1))
	      simplify
	      (instantiate-existential ("h(x_$3)"))
	      (block 
		(script-comment "`instantiate-existential' at (0 0 0)")
		(contrapose "with(p:prop,forall(y%iota:place,p));")
		(antecedent-inference "with(p:prop,forsome(x_$1:place,p));")
		(instantiate-existential ("x_$1"))
		(backchain "with(g:[place,place],f:sets[place],injective_on_q{g,f});")
		(apply-macete-with-minor-premises tr%domain-membership-iff-defined)
		direct-and-antecedent-inference-strategy)
	      (block 
		(script-comment "`instantiate-existential' at (0 1)")
		simplify
		(instantiate-existential ("x_$3"))))
	    (block 
	      (script-comment "`cut-with-single-formula' at (0)")
	      (apply-macete-with-minor-premises c%shadow-default)
	      (unfold-single-defined-constant (0 2) lower)
	      (cut-with-single-formula "x_$3 in bound%place(c%copy(sigma,lower(sigma,h%plus)))")
	      (block 
		(script-comment "`cut-with-single-formula' at (0)")
		(cut-with-single-formula "not((inverse{g}(h(x_$3))) in bound%place(c%copy(sigma,lower(sigma,h%plus))))")
		(block 
		  (script-comment "`cut-with-single-formula' at (0)")
		  (raise-conditional (0))
		  (raise-conditional (0))
		  direct-and-antecedent-inference-strategy
		  (block 
		    (script-comment "`direct-and-antecedent-inference-strategy' at (0 0)")
		    (contrapose "with(p:place,f:sets[place],not(p in f));")
		    beta-reduce-insistently)
		  (block 
		    (script-comment "`direct-and-antecedent-inference-strategy' at (0 1)")
		    (apply-macete-with-minor-premises default-c%copy-un-bound%place)
		    (backchain "with(f:[place,place],f)
=with(f:sets[place],
   lambda(p:place,
     with(p:prop,
       if(with(p:place,p in f),
         with(p:place,p),
         with(p:prop,p),
         with(p:place,p),
         with(p:place,p)))));")
		    beta-reduce
		    (backchain "with(h:[place,place],f:sets[place],h%plus:[place,place],
  h%plus=lambda(p:place,if(p in f, p, h(p))));")
		    beta-reduce
		    (raise-conditional (0))
		    direct-inference
		    (raise-conditional (0))
		    direct-inference
		    (raise-conditional (0))
		    direct-inference
		    (move-to-sibling 1)
		    (block 
		      (script-comment "`direct-inference' at (1)")
		      (contrapose "with(p:place,not(#(p)));")
		      (eliminate-defined-iota-expression 0
                                                                 
							 a))
		    (eliminate-defined-iota-expression 0
                                                                 
						       b)))
		(block 
		  (script-comment "`cut-with-single-formula' at (1)")
		  beta-reduce-insistently
		  (cut-with-single-formula "iota(y:place,g(y)=h(x_$3)) in dom{g}")
		  (move-to-sibling 1)
		  (block 
		    (script-comment "`cut-with-single-formula' at (1)")
		    (apply-macete-with-minor-premises tr%domain-membership-iff-defined)
		    simplify
		    (eliminate-defined-iota-expression 0
                                                                 
						       a))
		  (block 
		    (script-comment "`cut-with-single-formula' at (0)")
		    (cut-with-single-formula "dom{g} disj bound%place(c%copy(sigma,lower(sigma,h%plus)))")
		    (block 
		      (script-comment "`cut-with-single-formula' at (0)")
		      (contrapose "with(f:[place,place],sigma:istate,g:[place,place],
  dom{g} disj bound%place(c%copy(sigma,f)));")
		      auto-instantiate-existential)
		    (block 
		      (script-comment "`cut-with-single-formula' at (1)")
		      insistent-direct-and-antecedent-inference-strategy
		      (apply-macete-with-minor-premises bound%place-characterization)
		      beta-reduce-insistently
		      (apply-macete-with-minor-premises tr%definedness-of-dangling-conditionals)
		      (apply-macete-with-minor-premises gamma-c%copy-unchanged)
		      (unfold-single-defined-constant-globally c%copy)
		      (apply-macete-with-minor-premises lower-is-c%copy%fn)
		      (raise-conditional (0))
		      direct-inference
		      (contrapose "with(x_$0:place,g:[place,place],x_$0 in dom{g});")
		      (antecedent-inference "with(p:prop,if_form(p, p, p));")
		      (contrapose "with(x_$0:place,
  #(first%entry(with(f:[place,place],f),
                with(f:sets[place],f),
                x_$0)));")
		      (apply-macete-with-minor-premises tr%first%entry-equation)
		      beta-reduce-insistently
		      (apply-macete-with-minor-premises default%make-istate)
		      (apply-macete-with-minor-premises tr%definedness-of-dangling-conditionals)
		      (contrapose "with(x_$0:place,g:[place,place],x_$0 in dom{g});")
		      (move-to-ancestor 1)
		      (raise-conditional (0))
		      (contrapose "with(x_$0:place,g:[place,place],x_$0 in dom{g});")
		      (antecedent-inference "with(p:prop,if_form(p, p, p));")
		      (block 
			(script-comment "`antecedent-inference' at (0)")
                                                                 
			(contrapose "with(w:word,#(w));")
                                                                 
			(move-to-ancestor 1)
                                                                 
			(contrapose "with(f:[place,word],g:[place,place],
  dom{g} inters dom{f}=empty_indic{place});")
                                                                 
			extensionality
                                                                 
			beta-reduce
                                                                 
			(instantiate-existential ("x_$0"))
                                                                 
			beta-reduce
                                                                 
			simplify)
		      (block 
			(script-comment "`antecedent-inference' at (1)")
                                                                 
			(contrapose "with(p:place,
  #(first%entry(with(f:[place,place],f),
                with(f:sets[place],f),
                p)));")
                                                                 
			(unfold-single-defined-constant (1) lower)
                                                                 
			(backchain "with(h:[place,place],f:sets[place],h%plus:[place,place],
  h%plus=lambda(p:place,if(p in f, p, h(p))));")
                                                                 
			(backchain "with(h:[place,place],f:sets[place],h%plus:[place,place],
  h%plus=lambda(p:place,if(p in f, p, h(p))));")
                                                                 
			beta-reduce
                                                                 
			(force-substitution "if(x_$0 in bound%place(sigma),
                      default(sigma)(x_$0),
                      x_$0 in bound%place(sigma),
                      x_$0,
                      h(x_$0))"
					    "h(x_$0)"
					    (0))
                                                                 
			(move-to-sibling 1)
                                                                 
			(block 
			  (script-comment "`force-substitution' at (1)")
			  (instantiate-universal-antecedent "with(sigma:istate,g:[place,place],
  dom{g} disj bound%place(sigma));"
							    ("x_$0"))
			  (weaken (15 14 13 12 11 10 9 8 6 5 4 3))
			  simplify)
                                                                 
			(block 
			  (script-comment "`force-substitution' at (0)")
			  (cut-with-single-formula "not(#(h(x_$0)))")
			  (block 
			    (script-comment "`cut-with-single-formula' at (0)")
			    (weaken (14 13 12 11 10 9 8 6 5 4 3))
			    simplify)
			  (block 
			    (script-comment "`cut-with-single-formula' at (1)")
			    (instantiate-universal-antecedent "with(h,g:[place,place],dom{g} disj dom{h});"
							      ("x_$0"))
			    (apply-macete-with-minor-premises tr%rev%domain-membership-iff-defined))))))))
	      (block 
		(script-comment "`cut-with-single-formula' at (1)")
		(apply-macete-with-minor-premises default-in-bound-place-implies-bound)
		(unfold-single-defined-constant (0)
                                                                 
						c%copy)
		(apply-macete-with-minor-premises lower-is-c%copy%fn)
		(raise-conditional (0))
		(apply-macete-with-minor-premises default%make-istate)
		(unfold-single-defined-constant (0)
                                                                 
						lower)
		(backchain "with(h:[place,place],f:sets[place],h%plus:[place,place],
  h%plus=lambda(p:place,if(p in f, p, h(p))));")
		beta-reduce
		(raise-conditional (0))
		direct-and-antecedent-inference-strategy
		(block 
		  (script-comment "`direct-and-antecedent-inference-strategy' at (0 0)")
		  (contrapose "with(x_$3:place,sigma:istate,x_$3 in bound%place(sigma));")
		  (instantiate-universal-antecedent "with(sigma:istate,h:[place,place],
  dom{h} disj bound%place(sigma));"
                                                                 
						    ("x_$3")))
		(block 
		  (script-comment "`direct-and-antecedent-inference-strategy' at (0 1)")
		  (raise-conditional (0))
		  direct-inference
		  (apply-macete-with-minor-premises bound%place%stability)
		  (apply-macete-with-minor-premises c%copy-definedness)
		  direct-inference
		  (instantiate-universal-antecedent "with(f:sets[place],f subseteq f);"
                                                                 
						    ("(h(x_$3))"))
		  (contrapose "with(x_$3:place,h:[place,place],not(h(x_$3) in ran{h}));")
		  (apply-macete-with-minor-premises tr%in-range-condition)))))))))))






(def-theorem case-1-mach-copy
  "forall(sigma:istate, g, h, f, h%plus:[place -> place], v:sets[place],
  h%plus=lambda (p:place, if(p in bound%place(sigma), p, h(p)))
  and 
  copy%fn(abstr(sigma), h%plus)
  and 
  ran(h) subseteq bound%place(sigma)
  and 
  dom(h) disj bound%place(sigma)
  and 
  ran(h) disj ran(default(sigma)) 
  and 
  bijective_on_q{g,dom{g},ran{h}} 
  and
  dom(g) disj bound%place(sigma)
  and 
  dom(g) disj dom(h)
  and
  dom(g) disj ran(h)
  and 
  dom(g) disj v
  and 
  f=lambda(p:place, if(p in bound%place(c%copy(sigma,lower(sigma,h%plus))), p, #(g(p)), g(p),  ?place))
  implies 
  user%eq(
    a%copy(abstr(sigma), h%plus), 
    abstr(c%redirect( 
           c%shadow(c%copy(sigma,lower(sigma,h%plus)), f),
           (inverse{g} oo h))),
    v))"
  (theory places)
  (proof
   (
    (apply-macete-with-minor-premises c%redirect-no-op)
    (move-to-sibling 1)
    (block 
      (script-comment "`apply-macete-with-minor-premises' at (1)")
      (apply-macete-with-minor-premises c%redirect-c%shadow-c%copy-defined)
      auto-instantiate-existential)
    (block 
      (script-comment "`apply-macete-with-minor-premises' at (0)")
      (apply-macete-with-minor-premises rev%copy-liveness)
      (apply-macete-with-minor-premises c%shadow-no-op)
      (unfold-single-defined-constant-globally shadow%set)
      beta-reduce-with-minor-premises
      (move-to-sibling 1)
      (apply-macete-with-minor-premises c%copy-definedness)
      (block 
	(script-comment "`beta-reduce-with-minor-premises' at (0)")
	direct-and-antecedent-inference-strategy
	insistent-direct-and-antecedent-inference-strategy
	simplify-insistently
	(backchain "with(f:[place,place],f)
=with(f:sets[place],
   lambda(p:place,
     with(p:prop,
       if(with(p:place,p in f),
         with(p:place,p),
         with(p:prop,p),
         with(p:place,p),
         with(p:place,p)))));")
	beta-reduce
	(raise-conditional (0))
	direct-and-antecedent-inference-strategy
	(contrapose "with(p:place,#(p));")
	(move-to-ancestor 1)
	(instantiate-universal-antecedent "with(v:sets[place],g:[place,place],dom{g} disj v);"
					  ("x"))
	(contrapose "with(x:place,g:[place,place],not(x in dom{g}));")
	simplify)))))



(def-constant h%ok
  "lambda(h:[place->place], sigma:istate,    
     ran(h) subseteq bound%place(sigma)
     and 
     dom(h) disj bound%place(sigma))"
  (theory places))

(def-constant g%h%ok
  "lambda(g,h:[place->place], sigma:istate,   
     bijective_on_q{g,dom{g},ran{h}} 
     and
     dom(g) disj bound%place(sigma)
     and
     dom(g) disj dom{default(sigma)}
     and 
     dom(g) disj dom(h))"
  (theory places))

(def-theorem g%h%ok-corollary
  "forall(g,h:[place->place], sigma:istate,  
      h%ok(h, sigma) and g%h%ok(g,h, sigma)
      implies dom(g) disj ran(h))"
  (theory places)
  (proof
   (
    (unfold-single-defined-constant-globally h%ok)
    (unfold-single-defined-constant-globally g%h%ok)
    insistent-direct-and-antecedent-inference-strategy
    (backchain "with(f:sets[place],f subseteq f);")
    (backchain "with(sigma:istate,g:[place,place],
  dom{g} disj bound%place(sigma));"))))

(def-constant snapshot%not%visible
  "lambda(g:[place->place], v:sets[place], dom(g) disj v)"
  (theory places))

(def-theorem silly-conditional-simplification
  "forall(sigma:istate, g, h, f, h%plus:[place -> place], v:sets[place], 
     lambda(p:place,
       if(p in bound%place(c%copy(sigma,lower(sigma,h%plus))), p,
	  #(g(p)), g(p),  ?place))
    =lambda(p:place,
        if(p in bound%place(c%copy(sigma,lower(sigma,h%plus))), p,  g(p))))"
  (theory places)
  (proof ((prove-by-logic-and-simplification 0))))














(def-theorem case-1-mach-copy-thm
  "forall(sigma:istate, g, h, f, h%plus:[place -> place], v:sets[place],   
     h%ok(h,sigma)
     and 
     ran(h) disj ran(default(sigma)) 
     and 
     g%h%ok(g,h,sigma)
     and 
     snapshot%not%visible(g,v)
     and
     h%plus=lambda (p:place, if(p in bound%place(sigma), p, h(p)))
     and 
     copy%fn(abstr(sigma), h%plus)
     and 
     f=lambda(p:place, if(p in bound%place(c%copy(sigma,lower(sigma,h%plus))), p, g(p)))
     implies 
     user%eq(
       a%copy(abstr(sigma), h%plus), 
       abstr(c%redirect( 
              c%shadow(c%copy(sigma,lower(sigma,h%plus)), f),
              (inverse{g} oo h))),
       v))"
  (theory places)
  (proof
   (
    (apply-macete-with-minor-premises case-1-mach-copy)
    (apply-macete-with-minor-premises g%h%ok-corollary)
    (apply-macete-with-minor-premises silly-conditional-simplification)
    (unfold-single-defined-constant-globally g%h%ok)
    (unfold-single-defined-constant-globally h%ok)
    (unfold-single-defined-constant-globally snapshot%not%visible)
    insistent-direct-and-antecedent-inference-strategy
    auto-instantiate-existential
    insistent-direct-and-antecedent-inference-strategy)))

(def-theorem g%h%ok-dom-g-unbound
  "forall(sigma:istate, g,h:[place -> place], p:place, 
     h%ok(h,sigma)
     and 
     g%h%ok(g,h,sigma)
     and
     p in dom{g}
     implies 
     not p in bound%place(sigma))"
  (theory places)
  (proof
   (
    (unfold-single-defined-constant-globally h%ok)
    (unfold-single-defined-constant-globally g%h%ok)
    direct-and-antecedent-inference-strategy
    simplify)))

(def-theorem g%h%ok-dom-g-disj-dom-h
  "forall(sigma:istate, g,h:[place -> place], p:place,
     h%ok(h,sigma)
     and 
     g%h%ok(g,h,sigma)
     and 
     p in dom{g}
     implies 
     not p in dom{h})"
  (theory places)
  (proof
   (
    (unfold-single-defined-constant-globally g%h%ok)
    direct-and-antecedent-inference-strategy
    (backchain "with(h,g:[place,place],dom{g} disj dom{h});"))))

(def-theorem g%h%ok-dom-h-disj-dom-g
  "forall(sigma:istate, g,h:[place -> place], p:place,
     h%ok(h,sigma)
     and 
     g%h%ok(g,h,sigma)
     and p in dom{h}
     implies 
     not p in dom{g})"
  (theory places)
  (proof
   (
    (unfold-single-defined-constant-globally g%h%ok)
    direct-and-antecedent-inference-strategy
    (backchain "with(h,g:[place,place],dom{g} disj dom{h});"))))


(comment
 (def-theorem g%h%ok-dom-g-disj-dom-h_delta
   "forall(sigma:istate,g,h,h_delta:[place,place],p:place,
  h%ok(h,sigma)
   and 
  g%h%ok(g,h,sigma)
   and 
  h_delta
  =lambda(p:place,
     if(#(default(sigma)(p)),
       default(sigma)(p),
       h(p)))
   and 
  p in dom{g}
   implies 
  not(p in dom{h_delta}))"
   (theory places)
   (proof
    (    
     direct-and-antecedent-inference-strategy
     (backchain "with(f,h_delta:[place,place],h_delta=f);")
     beta-reduce-insistently
     simplify
     (raise-conditional (0))
     direct-and-antecedent-inference-strategy
     (block 
       (script-comment "`direct-and-antecedent-inference-strategy' at (0)")
       (instantiate-theorem g%h%ok-dom-g-unbound
			    ("sigma" "g" "h" "p"))
       (contrapose "with(p:prop,not(p));")
       (apply-macete-with-minor-premises bound%place-characterization)
       beta-reduce-insistently
       (apply-macete-with-minor-premises tr%first%entry-identity-in-set))
     (block 
       (script-comment "`direct-and-antecedent-inference-strategy' at (1)")
       simplify
       direct-and-antecedent-inference-strategy
       (block 
	 (script-comment "`direct-and-antecedent-inference-strategy' at (0)")
	 (contrapose "with(p:place,sigma:istate,p in bound%place(sigma));")
	 (apply-macete-with-minor-premises g%h%ok-dom-g-unbound)
	 auto-instantiate-existential)
       (block 
	 (script-comment "`direct-and-antecedent-inference-strategy' at (1)")
	 (apply-macete-with-minor-premises tr%rev%domain-membership-iff-defined)
	 (apply-macete-with-minor-premises g%h%ok-dom-g-disj-dom-h)
	 auto-instantiate-existential))))))

(comment
 (def-theorem g%h%ok-dom-h_delta-disj-dom-g
  "forall(sigma:istate, g,h,h_delta:[place -> place], p:place,
     h%ok(h,sigma)
     and 
     g%h%ok(g,h,sigma)
     and 
     h_delta=lambda(p:place, 
	      (#(default(sigma)(p)),
       default(sigma)(p),
       h(p)))
     and p in dom{h_delta}
     implies 
     not p in dom{g})"
  (theory places)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (contrapose "with(p:place,f:sets[place],p in f);")
    (apply-macete-with-minor-premises g%h%ok-dom-g-disj-dom-h_delta)
    auto-instantiate-existential))))


(def-theorem default-c%copy-lower
  "forall(sigma:istate,h%plus:[place,place],
      default(c%copy(sigma,lower(sigma,h%plus)))
      =lower(sigma,h%plus))"
  (theory places)
  (usages rewrite)
  (proof
   (
    (unfold-single-defined-constant-globally c%copy)
    (apply-macete-with-minor-premises lower-is-c%copy%fn)
    simplify)))

(def-theorem lower-for-bound-place
  "forall(sigma:istate, f:[place -> place], p:place, 
     p in bound%place(sigma) implies lower(sigma,f)(p)==default(sigma)(p))"
  (theory places)
  (proof
   (
    (unfold-single-defined-constant-globally lower)
    simplify)))

(def-theorem lower-for-unbound-place
  "forall(sigma:istate, f:[place -> place], p:place, 
     not(p in bound%place(sigma)) implies lower(sigma,f)(p)==f(p))"
  (theory places)
  (proof
   (
    (unfold-single-defined-constant-globally lower)
    simplify)))


(def-theorem preferred-c%shadow-c%copy-definedness
  "forall(f,h%plus:[place,place],g:[place,place],sigma:istate,h:[place,place],
  h%ok(h,sigma)
   and 
  g%h%ok(g,h,sigma)
   and 
  h%plus
  =lambda(p:place,if(p in bound%place(sigma), p, h(p)))
   and 
  copy%fn(abstr(sigma),h%plus)
   and 
  f
  =lambda(p:place,
     if(p in bound%place(c%copy(sigma,lower(sigma,h%plus))),
       p,
       g(p)))

  implies
  #(c%shadow(c%copy(sigma,lower(sigma,h%plus)),f)))"
  (theory places)
  (proof
   (
    (apply-macete-with-minor-premises c%shadow-c%copy-definedness)
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises silly-conditional-simplification)
    (instantiate-existential ("g" "h"))
    (block 
      (script-comment "`instantiate-existential' at (0 2)")
      (incorporate-antecedent "with(sigma:istate,h:[place,place],h%ok(h,sigma));")
      (unfold-single-defined-constant-globally h%ok)
      direct-and-antecedent-inference-strategy)
    (block 
      (script-comment "`instantiate-existential' at (0 3)")
      (incorporate-antecedent "with(sigma:istate,h,g:[place,place],g%h%ok(g,h,sigma));")
      (unfold-single-defined-constant-globally g%h%ok)
      direct-and-antecedent-inference-strategy))))


(def-theorem c%redirect-c%shadow-c%copy-definedness-case3
  "forall(sigma:istate, g,h,f,h%plus,h_delta:[place -> place], v:sets[place],
     h%ok(h,sigma)
     and 
     g%h%ok(g,h,sigma)
     and 
     snapshot%not%visible(g,v)
     and
     h%plus=lambda (p:place, if(p in bound%place(sigma), p, h(p)))
     and 
     copy%fn(abstr(sigma), h%plus)
     and 
     f=lambda(p:place, 
	if(p in bound%place(c%copy(sigma,lower(sigma,h%plus))), p, g(p)))
     implies 
     #(c%redirect(c%shadow(c%copy(sigma,lower(sigma,h%plus)),f),
               (inverse{g}) oo (lower(sigma,h%plus)))))"
  (theory places)
  (proof
   (
    (unfold-single-defined-constant-globally c%redirect)
    beta-reduce-with-minor-premises
    (move-to-sibling 1)
    (block 
      (script-comment "`beta-reduce-with-minor-premises' at (1)")
      (apply-macete-with-minor-premises preferred-c%shadow-c%copy-definedness)
      auto-instantiate-existential)
    (block 
      (script-comment "`beta-reduce-with-minor-premises' at (0)")
      simplify
      (unfold-single-defined-constant-globally c%redirect%fn)
      beta-reduce-with-minor-premises
      (move-to-sibling 1)
      (block 
	(script-comment "`beta-reduce-with-minor-premises' at (1)")
	(apply-macete-with-minor-premises preferred-c%shadow-c%copy-definedness)
	(instantiate-existential ("g" "h")))
      (block 
	(script-comment "`beta-reduce-with-minor-premises' at (0)")
	(apply-macete-with-minor-premises gamma-c%shadow-unchanged)
	(apply-macete-with-minor-premises gamma-c%copy-unchanged)
	(apply-macete-with-minor-premises c%shadow-default)
	(apply-macete-with-minor-premises tr%range-composition)
	(move-to-sibling 1)
	(block 
	  (script-comment "`apply-macete-with-minor-premises' at (1)")
	  (weaken (0 1))
	  (apply-macete-with-minor-premises tr%dom-of-inverse)
	  (block 
	    (script-comment "`apply-macete-with-minor-premises' at (0)")
	    (apply-macete-with-minor-premises tr%subseteq-transitivity)
	    (instantiate-existential ("ran{h}"))
	    (block 
	      (script-comment "`instantiate-existential' at (0 0 0)")
	      (antecedent-inference "with(p:prop,p);")
	      (incorporate-antecedent "with(sigma:istate,h,g:[place,place],g%h%ok(g,h,sigma));")
	      (unfold-single-defined-constant-globally g%h%ok)
	      direct-and-antecedent-inference-strategy
	      (backchain "with(h,g:[place,place],ran{g}=ran{h});"))
	    (block 
	      (script-comment "`instantiate-existential' at (0 0 1)")
	      (unfold-single-defined-constant-globally lower)
	      (backchain "with(p:prop,p and p and p and p and p and p);")
	      beta-reduce-insistently
	      simplify
	      direct-and-antecedent-inference-strategy
	      (instantiate-existential ("x"))
	      (raise-conditional (0))
	      direct-and-antecedent-inference-strategy
	      (antecedent-inference "with(p:prop,p and p and p and p and p and p);")
	      (contrapose "with(sigma:istate,h:[place,place],h%ok(h,sigma));")
	      (unfold-single-defined-constant-globally h%ok)
	      (contrapose "with(p,x_$3:place,x_$3=p);")
	      (auto-instantiate-universal-antecedent "with(h,g:[place,place],ran{g} subseteq ran{h});")
	      (antecedent-inference "with(p:prop,p and p);")
	      (auto-instantiate-universal-antecedent "with(sigma:istate,h:[place,place],
  dom{h} disj bound%place(sigma));")
	      (contrapose "with(x:place,f:sets[place],not(x in f));")
	      (apply-macete-with-minor-premises tr%domain-membership-iff-defined)))
	  (block 
	    (script-comment "`apply-macete-with-minor-premises' at (1)")
	    (antecedent-inference-strategy (0))
	    (apply-macete-with-minor-premises tr%injective-iff-injective-on-domain)
	    (incorporate-antecedent "with(sigma:istate,h,g:[place,place],g%h%ok(g,h,sigma));")
	    (unfold-single-defined-constant-globally g%h%ok)
	    direct-and-antecedent-inference-strategy))
	(move-to-ancestor 2)
	(move-to-descendent (1))
	(block 
	  (script-comment "`apply-macete-with-minor-premises' at (1)")
	  (apply-macete-with-minor-premises preferred-c%shadow-c%copy-definedness)
	  (instantiate-existential ("g" "h")))
	(move-to-ancestor 4)
	(move-to-descendent (1))
	(block 
	  (script-comment "`apply-macete-with-minor-premises' at (1)")
	  (apply-macete-with-minor-premises preferred-c%shadow-c%copy-definedness)
	  (instantiate-existential ("g" "h")))
	(move-to-ancestor 4)
	(move-to-descendent (2))
	(block 
	  (script-comment "`apply-macete-with-minor-premises' at (2)")
	  (apply-macete-with-minor-premises c%copy-definedness)
	  (antecedent-inference-strategy (1)))
	(block 
	  (script-comment "`apply-macete-with-minor-premises' at (0)")
	  (apply-macete-with-minor-premises tr%ran-of-inverse)
	  (move-to-sibling 1)
	  (block 
	    (script-comment "`apply-macete-with-minor-premises' at (1)")
	    (antecedent-inference-strategy (2))
	    (incorporate-antecedent "with(sigma:istate,h,g:[place,place],g%h%ok(g,h,sigma));")
	    (unfold-single-defined-constant-globally g%h%ok)
	    direct-and-antecedent-inference-strategy
	    (apply-macete-with-minor-premises tr%injective-iff-injective-on-domain))
	  (block 
	    (script-comment "`apply-macete-with-minor-premises' at (0)")
	    simplify-insistently
	    direct-and-antecedent-inference-strategy
	    (block 
	      (script-comment "`direct-and-antecedent-inference-strategy' at (0 0 0 0 0 0)")
	      extensionality
	      simplify-insistently
	      (incorporate-antecedent "with(sigma:istate,h,g:[place,place],g%h%ok(g,h,sigma));")
	      (unfold-single-defined-constant-globally g%h%ok)
	      direct-and-antecedent-inference-strategy
	      (instantiate-universal-antecedent "with(sigma:istate,g:[place,place],
  dom{g} disj bound%place(sigma));"
                                                                 
						("x_0"))
	      (block 
		(script-comment "`instantiate-universal-antecedent' at (0 0 0)")
		(contrapose "with(p:prop,not(p));")
		(apply-macete-with-minor-premises tr%domain-membership-iff-defined))
	      (block 
		(script-comment "`instantiate-universal-antecedent' at (0 0 1)")
		(contrapose "with(p:prop,not(p));")
		(apply-macete-with-minor-premises bound%place-characterization)
		beta-reduce-insistently
		(apply-macete-with-minor-premises tr%first%entry-identity-in-set)))
	    (block 
	      (script-comment "`direct-and-antecedent-inference-strategy' at (0 0 1 0 0 0)")
	      extensionality
	      simplify-insistently
	      direct-and-antecedent-inference-strategy
	      (cut-with-single-formula "#(lower(sigma,h%plus)(x_0))")
	      (contrapose "with(x_0:place,h%plus:[place,place],sigma:istate,
  #(lower(sigma,h%plus)(x_0)));")
	      (unfold-single-defined-constant-globally lower)
	      (backchain "with(h:[place,place],sigma:istate,h%plus:[place,place],
  h%plus
  =lambda(p:place,if(p in bound%place(sigma), p, h(p))));")
	      beta-reduce
	      (raise-conditional (0))
	      (raise-conditional (0))
	      (contrapose "with(sigma:istate,h,g:[place,place],g%h%ok(g,h,sigma));")
	      (unfold-single-defined-constant-globally g%h%ok)
	      (antecedent-inference-strategy (0))
	      (block 
		(script-comment "`antecedent-inference-strategy' at (0)")
		(contrapose "with(x_0:place,f:sets[place],x_0 in f);")
		(backchain "with(p:prop,p and p and p and p);")
		(move-to-ancestor 1)
		(antecedent-inference-strategy (0))
		(auto-instantiate-universal-antecedent "with(sigma:istate,g:[place,place],
  dom{g} disj bound%place(sigma));")
		(instantiate-universal-antecedent "with(sigma:istate,g:[place,place],
  dom{g} disj bound%place(sigma));"
                                                                 
						  ("x_0"))
		(contrapose "with(p:prop,not(p));")
		(apply-macete-with-minor-premises tr%domain-membership-iff-defined))
	      (block 
		(script-comment "`antecedent-inference-strategy' at (1 1)")
		(contrapose "with(x_0:place,h:[place,place],#(h(x_0)));")
		(antecedent-inference-strategy (0))
		(instantiate-universal-antecedent "with(h,g:[place,place],dom{g} disj dom{h});"
                                                                 
						  ("x_0"))
		(block 
		  (script-comment "`instantiate-universal-antecedent' at (0 0 0)")
		  (contrapose "with(x_0:place,g:[place,place],not(x_0 in dom{g}));")
		  (apply-macete-with-minor-premises tr%domain-membership-iff-defined))
		(block 
		  (script-comment "`instantiate-universal-antecedent' at (0 0 1)")
		  (contrapose "with(x_0:place,h:[place,place],not(x_0 in dom{h}));")
		  (apply-macete-with-minor-premises tr%domain-membership-iff-defined))))
	    (block 
	      (script-comment "`direct-and-antecedent-inference-strategy' at (0 0 2 0 0 0 0 0)")
	      (cut-with-single-formula "x_$3 in bound%place(c%copy(sigma,lower(sigma,h%plus)))")
	      (move-to-sibling 1)
	      (block 
		(script-comment "`cut-with-single-formula' at (1)")
		(cut-with-single-formula "#(lower(sigma,h%plus)(x_$3))")
		(move-to-sibling 1)
		simplify
		(block 
		  (script-comment "`cut-with-single-formula' at (0)")
		  (incorporate-antecedent "with(x_$3:place,h%plus:[place,place],sigma:istate,
  #(lower(sigma,h%plus)(x_$3)));")
		  (unfold-single-defined-constant (0)
                                                                 
						  lower)
		  (backchain "with(h:[place,place],sigma:istate,h%plus:[place,place],
  h%plus
  =lambda(p:place,if(p in bound%place(sigma), p, h(p))));")
		  beta-reduce
		  (raise-conditional (0))
		  (raise-conditional (0))
		  direct-and-antecedent-inference-strategy
		  (block 
		    (script-comment "`direct-and-antecedent-inference-strategy' at (0 0)")
		    (apply-macete-with-minor-premises bound%place%stability)
		    (apply-macete-with-minor-premises c%copy-definedness)
		    direct-and-antecedent-inference-strategy)
		  (block 
		    (script-comment "`direct-and-antecedent-inference-strategy' at (0 1 1)")
		    (apply-macete-with-minor-premises bound%place-characterization)
		    (block 
		      (script-comment "`apply-macete-with-minor-premises' at (0)")
		      beta-reduce-insistently
		      (apply-macete-with-minor-premises gamma-c%copy-unchanged)
		      (move-to-ancestor 1)
		      (apply-macete-with-minor-premises tr%definedness-of-dangling-conditionals)
		      (apply-macete-with-minor-premises tr%first%entry-equation)
		      (raise-conditional (0))
		      direct-and-antecedent-inference-strategy
		      (apply-macete-locally-with-minor-premises default-c%copy-lower
                                                                 
								(0)
                                                                 
								"default(c%copy(sigma,lower(sigma,h%plus)))
                 (x_$3)")
		      (apply-macete-with-minor-premises lower-for-unbound-place)
		      (force-substitution "h%plus(x_$3)"
                                                                 
					  "if(x_$3 in bound%place(sigma), x_$3, h(x_$3))"
                                                                 
					  (0))
		      (block 
			(script-comment "`force-substitution' at (0)")
                                                                 
			simplify
                                                                 
			(move-to-ancestor 1)
                                                                 
			(raise-conditional (1))
                                                                 
			direct-and-antecedent-inference-strategy
                                                                 
			(cut-with-single-formula "h(x_$3) in bound%place(c%copy(sigma,lower(sigma,h%plus)))")
                                                                 
			(block 
			  (script-comment "`cut-with-single-formula' at (0)")
			  (incorporate-antecedent "with(p:place,f:sets[place],p in f);")
			  (apply-macete-with-minor-premises bound%place-characterization)
			  beta-reduce-insistently
			  (apply-macete-with-minor-premises tr%definedness-of-dangling-conditionals))
                                                                 
			(block 
			  (script-comment "`cut-with-single-formula' at (1)")
			  (incorporate-antecedent "with(sigma:istate,h:[place,place],h%ok(h,sigma));")
			  (unfold-single-defined-constant-globally h%ok)
			  direct-and-antecedent-inference-strategy
			  (instantiate-universal-antecedent "with(f:sets[place],f subseteq f);"
							    ("h(x_$3)"))
			  (block 
			    (script-comment "`instantiate-universal-antecedent' at (0 0 0)")
			    (contrapose "with(x_$3:place,h:[place,place],not(h(x_$3) in ran{h}));")
			    (apply-macete-with-minor-premises tr%in-range-condition))
			  (block 
			    (script-comment "`instantiate-universal-antecedent' at (0 0 1)")
			    (apply-macete-with-minor-premises bound%place%stability)
			    (apply-macete-with-minor-premises c%copy-definedness)
			    direct-and-antecedent-inference-strategy)))
		      (block 
			(script-comment "`force-substitution' at (1)")
                                                                 
			(backchain "with(h:[place,place],sigma:istate,h%plus:[place,place],
  h%plus
  =lambda(p:place,if(p in bound%place(sigma), p, h(p))));")
                                                                 
			beta-reduce))
		    (apply-macete-with-minor-premises c%copy-definedness))))
	      (block 
		(script-comment "`cut-with-single-formula' at (0)")
		(apply-macete-locally-with-minor-premises lower-for-bound-place
                                                                 
							  (0)
                                                                 
							  "lower(c%copy(sigma,lower(sigma,h%plus)),f)(x_$3)")
		(apply-macete-with-minor-premises default-c%copy-lower)
		(cut-with-single-formula "not((iota(y:place,g(y)=lower(sigma,h%plus)(x_$3))) in bound%place(c%copy(sigma,lower(sigma,h%plus))))")
		(block 
		  (script-comment "`cut-with-single-formula' at (0)")
		  (apply-macete-locally-with-minor-premises lower-for-unbound-place
                                                                 
							    (0)
                                                                 
							    "lower(c%copy(sigma,lower(sigma,h%plus)),f)
    (iota(y:place,g(y)=lower(sigma,h%plus)(x_$3)))")
		  (backchain "with(g:[place,place],sigma:istate,f:[place,place],
  f
  =lambda(p:place,
     if(p in bound%place(c%copy(sigma,f)), p, g(p))));")
		  beta-reduce-with-minor-premises
		  (raise-conditional (0))
		  direct-and-antecedent-inference-strategy
		  (cut-with-single-formula "#(iota(y:place,g(y)=lower(sigma,h%plus)(x_$3)))")
		  (eliminate-defined-iota-expression 0
                                                                 
						     a)
		  (block 
		    (script-comment "`beta-reduce-with-minor-premises' at (0 0 1 1)")
		    (cut-with-single-formula "#(lower(sigma,h%plus)(x_$3))")
		    (incorporate-antecedent "with(x_$3:place,f,g:[place,place],#(inverse{g}(f(x_$3))));")
		    simplify-insistently))
		(block 
		  (script-comment "`cut-with-single-formula' at (1)")
		  (cut-with-single-formula "#(lower(sigma,h%plus)(x_$3))")
		  (incorporate-antecedent "with(x_$3:place,f,g:[place,place],#(inverse{g}(f(x_$3))));")
		  simplify
		  direct-inference
		  (eliminate-defined-iota-expression 0
                                                                 
						     a)
		  (incorporate-antecedent "with(sigma:istate,h,g:[place,place],g%h%ok(g,h,sigma));")
		  (unfold-single-defined-constant-globally g%h%ok)
		  direct-and-antecedent-inference-strategy
		  (instantiate-universal-antecedent "with(sigma:istate,g:[place,place],
  dom{g} disj bound%place(sigma));"
                                                                 
						    ("a"))
		  (block 
		    (script-comment "`instantiate-universal-antecedent' at (0 0 0)")
		    (contrapose "with(p:prop,not(p));")
		    (apply-macete-with-minor-premises tr%domain-membership-iff-defined))
		  (block 
		    (script-comment "`instantiate-universal-antecedent' at (0 0 1)")
		    (apply-macete-with-minor-premises bound%place-characterization)
		    beta-reduce-insistently
		    (apply-macete-with-minor-premises tr%definedness-of-dangling-conditionals)
		    (apply-macete-with-minor-premises tr%first%entry-equation)
		    simplify
		    direct-inference
		    (block 
		      (script-comment "`direct-inference' at (0)")
		      (contrapose "with(p:prop,not(p));")
		      (apply-macete-with-minor-premises bound%place-characterization)
		      beta-reduce-insistently
		      (apply-macete-with-minor-premises tr%first%entry-identity-in-set))
		    (block 
		      (script-comment "`direct-inference' at (1)")
		      (unfold-single-defined-constant (1)
                                                                 
						      lower)
		      (backchain "with(h:[place,place],sigma:istate,h%plus:[place,place],
  h%plus
  =lambda(p:place,if(p in bound%place(sigma), p, h(p))));")
		      (move-to-ancestor 1)
		      (force-substitution "h%plus(a)"
                                                                 
					  "if(a in bound%place(sigma), a, h(a))"
                                                                 
					  (0))
		      (block 
			(script-comment "`force-substitution' at (0)")
                                                                 
			simplify
                                                                 
			(instantiate-universal-antecedent "with(h,g:[place,place],dom{g} disj dom{h});"
							  ("a"))
                                                                 
			(block 
			  (script-comment "`instantiate-universal-antecedent' at (0 0 0)")
			  (contrapose "with(a:place,g:[place,place],not(a in dom{g}));")
			  (apply-macete-with-minor-premises tr%domain-membership-iff-defined))
                                                                 
			(block 
			  (script-comment "`instantiate-universal-antecedent' at (0 0 1)")
			  (contrapose "with(a:place,h:[place,place],not(a in dom{h}));")
			  (apply-macete-with-minor-premises tr%domain-membership-iff-defined)))
		      (block 
			(script-comment "`force-substitution' at (1)")
                                                                 
			(backchain "with(h:[place,place],sigma:istate,h%plus:[place,place],
  h%plus
  =lambda(p:place,if(p in bound%place(sigma), p, h(p))));")
                                                                 
			beta-reduce)))))))))))))

(def-theorem case-3-mach-copy-thm
  "forall(sigma:istate, g,h,f,h%plus,h_delta:[place -> place], v:sets[place],
     h%ok(h,sigma)
     and 
     g%h%ok(g,h,sigma)
     and 
     snapshot%not%visible(g,v)
     and
     h%plus=lambda (p:place, if(p in bound%place(sigma), p, h(p)))
     and 
     copy%fn(abstr(sigma), h%plus)
     and 
     f=lambda(p:place, 
	if(p in bound%place(c%copy(sigma,lower(sigma,h%plus))), p, g(p)))
     implies 
     user%eq(
       a%copy(abstr(sigma), h%plus), 
       abstr(c%redirect( 
              c%shadow(c%copy(sigma,lower(sigma,h%plus)), f),
              (inverse{g}) oo (lower(sigma,h%plus)))),
       v))"
  (theory places)
  (proof
   (
    (apply-macete-with-minor-premises c%redirect-no-op)
    (block 
      (script-comment "`apply-macete-with-minor-premises' at (0)")
      (apply-macete-with-minor-premises rev%copy-liveness)
      (apply-macete-with-minor-premises c%shadow-no-op)
      (unfold-single-defined-constant-globally c%shadow)
      beta-reduce-with-minor-premises
      (move-to-sibling 1)
      (apply-macete-with-minor-premises c%copy-definedness)
      (block 
	(script-comment "`beta-reduce-with-minor-premises' at (0)")
	insistent-direct-and-antecedent-inference-strategy
	(block 
	  (script-comment "`insistent-direct-and-antecedent-inference-strategy' at (0 0 0 0 0
0)")
	  (unfold-single-defined-constant-globally shadow%set)
	  beta-reduce-with-minor-premises
	  (move-to-sibling 1)
	  (apply-macete-with-minor-premises c%copy-definedness)
	  (block 
	    (script-comment "`beta-reduce-with-minor-premises' at (0)")
	    simplify-insistently
	    (backchain "with(g:[place,place],sigma:istate,f:[place,place],
  f
  =lambda(p:place,
     if(p in bound%place(c%copy(sigma,f)), p, g(p))));")
	    (backchain "with(h:[place,place],sigma:istate,h%plus:[place,place],
  h%plus
  =lambda(p:place,if(p in bound%place(sigma), p, h(p))));")
	    (move-to-ancestor 1)
	    beta-reduce
	    (raise-conditional (0))
	    direct-and-antecedent-inference-strategy
	    (contrapose "with(v:sets[place],g:[place,place],
  snapshot%not%visible(g,v));")
	    (unfold-single-defined-constant-globally snapshot%not%visible)
	    simplify-insistently
	    auto-instantiate-existential))
	(block 
	  (script-comment "`insistent-direct-and-antecedent-inference-strategy' at (0 0 1 0)")
	  simplify
	  (apply-macete-with-minor-premises c%copy-definedness)
	  (apply-macete-with-minor-premises a%copy-definedness)
	  direct-inference
	  (apply-macete-with-minor-premises copy-liveness)
	  (unfold-single-defined-constant-globally copy%fn)
	  (force-substitution "dom{a%copy(abstr(sigma),h%plus)}"
			      "bound%place(c%copy(sigma,lower(sigma,h%plus)))"
			      (0 1))
	  (move-to-sibling 1)
	  (block 
	    (script-comment "`force-substitution' at (1)")
	    (apply-macete-with-minor-premises rev%copy-liveness)
	    (unfold-single-defined-constant-globally bound%place)
	    (move-to-ancestor 1)
	    extensionality
	    (block 
	      (script-comment "`extensionality' at (0)")
	      beta-reduce
	      simplify
	      (apply-macete-with-minor-premises tr%value-of-a-defined-indicator-application)
	      (block 
		(script-comment "`apply-macete-with-minor-premises' at (0)")
		(apply-macete-with-minor-premises bound%place-abstr-definedness)
		direct-and-antecedent-inference-strategy)
	      (apply-macete-with-minor-premises bound%place-abstr-definedness))
	    (block 
	      (script-comment "`extensionality' at (1)")
	      (apply-macete-with-minor-premises bound%place-characterization)
	      (apply-macete-with-minor-premises c%copy-definedness)))
	  (block 
	    (script-comment "`force-substitution' at (0)")
	    (backchain-repeatedly ("with(g,h%plus:[place,place],sigma:istate,f:[place,place],
  f
  =lambda(p:place,
     if(p in bound%place(c%copy(sigma,lower(sigma,h%plus))),
       p,
       g(p))));"))
	    beta-reduce
	    simplify
	    (backchain "with(g:[place,place],sigma:istate,f:[place,place],
  f
  =lambda(p:place,
     if(p in bound%place(c%copy(sigma,f)), p, g(p))));")
	    beta-reduce-insistently
	    simplify
	    (raise-conditional (0))
	    direct-and-antecedent-inference-strategy
	    simplify
	    (block 
	      (script-comment "`direct-and-antecedent-inference-strategy' at (0 0 0 1)")
	      (incorporate-antecedent "with(sigma:istate,h,g:[place,place],g%h%ok(g,h,sigma));")
	      (unfold-single-defined-constant-globally g%h%ok)
	      direct-and-antecedent-inference-strategy
	      (cut-with-single-formula "x_$0 in ran{h}")
	      (block 
		(script-comment "`cut-with-single-formula' at (0)")
		(incorporate-antecedent "with(sigma:istate,h:[place,place],h%ok(h,sigma));")
		(unfold-single-defined-constant-globally h%ok)
		direct-and-antecedent-inference-strategy
		(apply-macete-with-minor-premises bound%place%stability)
		(apply-macete-with-minor-premises c%copy-definedness)
		direct-inference
		(backchain "with(f:sets[place],f subseteq f);"))
	      (block 
		(script-comment "`cut-with-single-formula' at (1)")
		(backchain-backwards "with(h,g:[place,place],ran{g}=ran{h});")
		(backchain "with(p,x_$0:place,x_$0=p);")
		(apply-macete-with-minor-premises tr%in-range-condition)))))))
    (block 
      (script-comment "`apply-macete-with-minor-premises' at (1)")
      (apply-macete-with-minor-premises c%redirect-c%shadow-c%copy-definedness-case3)
      auto-instantiate-existential))))



(def-constant g%h%ok_2
  "lambda(g,h:[place->place], s:sets[place], sigma:istate,   
     bijective_on_q{g,s,ran{h}} 
     and
     dom(g) disj dom{gamma(sigma)}
     and 
     dom(g) disj dom(h)
     and 
     forall(p:place, #(g(p)) implies g(p)=default(sigma)(p)))"
  (theory places))

(def-theorem empty-inters-iff-disjoint
  "forall(s_0,s_1:sets[ind_1], 
      s_0 inters s_1=empty_indic{ind_1}
       iff s_0 disj s_1)"
  (theory pure-generic-theory-1)
  (usages transportable-rewrite transportable-macete)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (0 0)")
      (contrapose "with(p:prop,p);")
      extensionality
      simplify-insistently)
    (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (0 1)")
      extensionality
      simplify-insistently))))

(def-theorem lower-h%plus
  "forall(sigma:istate,h,h%plus:[place,place],
    h%plus
    =lambda(p:place,if(p in bound%place(sigma), p, h(p)))
     implies 
    lower(sigma,h%plus)=lower(sigma,h))"
  (theory places)
  (proof
   (
    (unfold-single-defined-constant-globally lower)
    direct-and-antecedent-inference-strategy
    (backchain "with(p:prop,p);")
    extensionality
    beta-reduce
    direct-inference
    (case-split-on-conditionals (0)))))

(def-theorem g%h%ok_2-etc-implies-bound
  "forall(sigma:istate,g,h:[place,place],s:sets[place],a:place,
  g%h%ok_2(g,h,s,sigma) and h%ok(h,sigma) and a in s
   implies 
  a in bound%place(sigma))"
  (theory places)
  (proof
   (
    (unfold-single-defined-constant-globally g%h%ok_2)
    (unfold-single-defined-constant-globally h%ok)
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "default(sigma)(a) in bound%place(sigma)")
    (apply-macete-with-minor-premises default-in-bound-place-implies-bound)
    (block 
      (script-comment "`cut-with-single-formula' at (1)")
      (backchain-backwards "forall(p:place,#(p) implies p=p);")
      direct-inference
      (block 
	(script-comment "`direct-inference' at (0)")
	(apply-macete-with-minor-premises tr%rev%domain-membership-iff-defined)
	simplify)
      (block 
	(script-comment "`direct-inference' at (1)")
	(cut-with-single-formula "g(a) in ran{g}")
	(move-to-sibling 1)
	(apply-macete-with-minor-premises tr%in-range-condition)
	(block 
	  (script-comment "`cut-with-single-formula' at (0)")
	  (apply-macete-with-minor-premises tr%element-of-a-subset-is-an-element)
	  auto-instantiate-existential
	  (backchain "with(h,g:[place,place],ran{g}=ran{h});")))))))

(def-theorem g%h%ok_2-disjointness
  "forall(sigma:istate, g,h:[place -> place], s:sets[place], 
  g%h%ok_2(g,h,s,sigma) implies dom{g} disj dom{h})"
  (theory places)
  (proof
   (
    (unfold-single-defined-constant-globally g%h%ok_2)
    direct-and-antecedent-inference-strategy)))

(def-theorem h%ok-implies-dom-unbound
  "forall(sigma:istate, h:[place -> place], a:place,
  h%ok(h,sigma) and a in dom{h} implies not(a in bound%place(sigma)))"
  (theory places)
  (proof
   (
    (unfold-single-defined-constant-globally h%ok)
    simplify
    (move-to-ancestor 1)
    direct-and-antecedent-inference-strategy
    (backchain "with(f:sets[place],f disj f);"))))

(def-theorem g%h%ok_2-iota-definedness
  "forall(sigma:istate, g,h:[place -> place], s:sets[place], x:place, 
  g%h%ok_2(g,h,s,sigma) and x in dom{h} implies #(iota(y:place,g(y)=h(x))))"
  (theory places)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (incorporate-antecedent "with(sigma:istate,s:sets[place],h,g:[place,place],
  g%h%ok_2(g,h,s,sigma));")
    (unfold-single-defined-constant-globally g%h%ok_2)
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "#(h(x))")
    (move-to-sibling 1)
    (apply-macete-with-minor-premises tr%rev%domain-membership-iff-defined)
    (block 
      (script-comment "`cut-with-single-formula' at (0)")
      (eliminate-iota 0)
      (contrapose "with(h,g:[place,place],ran{g}=ran{h});")
      extensionality
      beta-reduce-insistently
      (instantiate-existential ("h(x)"))
      simplify
      direct-inference
      (move-to-sibling 1)
      (instantiate-existential ("x"))
      (block 
	(script-comment "`direct-inference' at (0)")
	(contrapose "with(p:prop,forall(y%iota:place,p or p or p));")
	(antecedent-inference-strategy (0 1))
	(instantiate-existential ("x_$1"))
	(backchain "with(g:[place,place],s:sets[place],injective_on_q{g,s});")
	(force-substitution "s" "dom{g}" (0 1))
	(apply-macete-with-minor-premises tr%domain-membership-iff-defined)
	simplify)))))

(def-theorem case-2-mach-copy-thm
  "forall(sigma:istate,g,h,h%plus:[place,place],s,v:sets[place],
  h%ok(h,sigma)
   and 
  g%h%ok_2(g,h,s,sigma)
   and 
  snapshot%not%visible(g,v)
   and 
  h%plus
  =lambda(p:place,if(p in bound%place(sigma), p, h(p)))
   and 
  copy%fn(abstr(sigma),h%plus)
   implies 
  user%eq(a%copy(abstr(sigma),h%plus),
          abstr(c%redirect(c%copy(sigma,lower(sigma,h%plus)),
                           (inverse{g}) oo h)),
          v))"
  (theory places)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises c%redirect-no-op)
    (block 
      (script-comment "`apply-macete-with-minor-premises' at (0)")
      (apply-macete-with-minor-premises copy-liveness)
      (unfold-single-defined-constant-globally user%eq))
    (block 
      (script-comment "`apply-macete-with-minor-premises' at (1)")
      (unfold-single-defined-constant-globally c%redirect)
      simplify
      (unfold-single-defined-constant-globally c%redirect%fn)
      (apply-macete-with-minor-premises tr%range-composition)
      (apply-macete-with-minor-premises tr%ran-of-inverse)
      (apply-macete-with-minor-premises gamma-c%copy-unchanged)
      (apply-macete-with-minor-premises tr%domain-composition)
      (move-to-ancestor 4)
      (move-to-descendent (1))
      (block 
	(script-comment "`apply-macete-with-minor-premises' at (1)")
	(weaken (0 1))
	(move-to-ancestor 2)
	(move-to-descendent (0 1))
	(block 
	  (script-comment "`apply-macete-with-minor-premises' at (1)")
	  (weaken (0 1))
	  (move-to-ancestor 2)
	  (move-to-descendent (0 0 1))
	  (weaken (1))
	  (move-to-ancestor 2)
	  (move-to-descendent (0))
	  (block 
	    (script-comment "`apply-macete-with-minor-premises' at (0)")
	    (apply-macete-locally-with-minor-premises tr%intersection-commutativity
                                                                 
						      (0)
                                                                 
						      "dom{h} inters dom{g}=empty_indic{place}")
	    (apply-macete-with-minor-premises tr%empty-inters-iff-disjoint)
	    (incorporate-antecedent "with(sigma:istate,s:sets[place],h,g:[place,place],
  g%h%ok_2(g,h,s,sigma));")
	    (unfold-single-defined-constant-globally g%h%ok_2)
	    direct-and-antecedent-inference-strategy
	    (apply-macete-with-minor-premises default-c%copy-lower)
	    (instantiate-theorem lower-h%plus
				 ("sigma" "h" "h%plus"))
	    (backchain-repeatedly ("with(h,h%plus:[place,place],sigma:istate,
  lower(sigma,h%plus)=lower(sigma,h));"))
	    (unfold-single-defined-constant-globally lower)
	    (instantiate-theorem h%ok-implies-dom-unbound
				 ("sigma" "h" "x_$3"))
	    (instantiate-theorem g%h%ok_2-iota-definedness
				 ("sigma" "g" "h" "s" "x_$3"))
	    (block 
	      (script-comment "`instantiate-theorem' at (0 0 0)")
	      (contrapose "with(sigma:istate,s:sets[place],h,g:[place,place],
  not(g%h%ok_2(g,h,s,sigma)));")
	      (unfold-single-defined-constant-globally g%h%ok_2)
	      direct-and-antecedent-inference-strategy
	      insistent-direct-and-antecedent-inference-strategy)
	    (block 
	      (script-comment "`instantiate-theorem' at (0 1)")
	      simplify-insistently
	      beta-reduce-insistently
	      (cut-with-single-formula "#(h(x_$3))")
	      (move-to-sibling 1)
	      (apply-macete-with-minor-premises tr%rev%domain-membership-iff-defined)
	      (block 
		(script-comment "`cut-with-single-formula' at (0)")
		beta-reduce-insistently
		(apply-macete-with-minor-premises g%h%ok_2-etc-implies-bound)
		(instantiate-theorem g%h%ok_2-etc-implies-bound
				     ("sigma" "g"
                                                                 
					      "h"
                                                                 
					      "s"
                                                                 
					      "iota(y:place,g(y)=h(x_$3))"))
		(block 
		  (script-comment "`instantiate-theorem' at (0 0 0)")
		  (contrapose "with(sigma:istate,s:sets[place],h,g:[place,place],
  not(g%h%ok_2(g,h,s,sigma)));")
		  (unfold-single-defined-constant-globally g%h%ok_2)
		  insistent-direct-and-antecedent-inference-strategy)
		(block 
		  (script-comment "`instantiate-theorem' at (0 0 2)")
		  (contrapose "with(p:prop,s:sets[place],not(iota(y:place,p) in s));")
		  (eliminate-defined-iota-expression 0
                                                                 
						     b)
		  (backchain-backwards "with(s:sets[place],g:[place,place],dom{g}=s);")
		  (apply-macete-with-minor-premises tr%domain-membership-iff-defined))
		(block 
		  (script-comment "`instantiate-theorem' at (0 1)")
		  (raise-conditional (0))
		  direct-and-antecedent-inference-strategy
		  (backchain-backwards "with(p:prop,forall(p:place,with(p:prop,p implies p)));")
		  direct-inference
		  (eliminate-defined-iota-expression 0
                                                                 
						     c)
		  (eliminate-defined-iota-expression 0
                                                                 
						     d)))))
	  (block 
	    (script-comment "`apply-macete-with-minor-premises' at (1 0)")
	    (apply-macete-with-minor-premises tr%dom-of-inverse)
	    (block 
	      (script-comment "`apply-macete-with-minor-premises' at (0)")
	      (incorporate-antecedent "with(sigma:istate,s:sets[place],h,g:[place,place],
  g%h%ok_2(g,h,s,sigma));")
	      (unfold-single-defined-constant-globally g%h%ok_2)
	      direct-and-antecedent-inference-strategy
	      (backchain "with(h,g:[place,place],ran{g}=ran{h});"))
	    (block 
	      (script-comment "`apply-macete-with-minor-premises' at (1)")
	      (weaken (0 1))
	      (incorporate-antecedent "with(sigma:istate,s:sets[place],h,g:[place,place],
  g%h%ok_2(g,h,s,sigma));")
	      (unfold-single-defined-constant-globally g%h%ok_2)
	      direct-and-antecedent-inference-strategy
	      (apply-macete-with-minor-premises tr%injective-iff-injective-on-domain)
	      (backchain "with(s:sets[place],g:[place,place],dom{g}=s);"))))
	(block 
	  (script-comment "`apply-macete-with-minor-premises' at (1 0)")
	  (apply-macete-with-minor-premises tr%dom-of-inverse)
	  (incorporate-antecedent "with(sigma:istate,s:sets[place],h,g:[place,place],
  g%h%ok_2(g,h,s,sigma));")
	  (unfold-single-defined-constant-globally g%h%ok_2)
	  direct-and-antecedent-inference-strategy
	  (backchain "with(h,g:[place,place],ran{g}=ran{h});")))))))

