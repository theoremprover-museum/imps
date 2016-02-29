(include-files (files (imps theories/vmach/places)))

(def-theorem bound%place-totality
  "forall(sigma:istate,#(bound%place(sigma)))"
  (theory places)
  (usages d-r-convergence)
  (proof
   (
    (unfold-single-defined-constant-globally bound%place)
    simplify-insistently)))

(def-theorem raise-totality
  "forall(f:[place,place],sigma:istate,#(raise(sigma,f)))"
  (theory places)
  (usages d-r-convergence)
  (proof
   (
    (unfold-single-defined-constant-globally raise))))

(def-theorem bound%place-abstr-definedness
  "forall(sigma:istate, p:place, 
	p in bound%place(sigma) iff #(abstr(sigma)(p)))"
  reverse
  (theory places)
  (proof
   (
    (unfold-single-defined-constant-globally bound%place)
    (unfold-single-defined-constant-globally abstr)
    (apply-macete-with-minor-premises tr%domain-membership-iff-defined)
    simplify)))

(comment 
 (def-theorem first%entry-in-set
  "forall(f:[ind_1->ind_1], s:sets[ind_1], x:ind_1, 
     #(first%entry(f,s,x)) implies 
     (first%entry(f,s,x) in s))"
  
  (theory generic-theory-1)
  (usages transportable-macete)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (instantiate-theorem first%entry-characterization
			 ("f" "s" "x" "first%entry(f,s,x)"))))))

(def-theorem first%entry-identity-in-set
  "forall(f:[ind_1->ind_1], s:sets[ind_1], x:ind_1, 
     x in s implies first%entry(f,s,x)=x)"
  (theory generic-theory-1)
  (usages transportable-macete)
  (proof
   (
    (apply-macete-with-minor-premises first%entry-characterization)
    direct-and-antecedent-inference-strategy
    (instantiate-existential ("0"))
    (unfold-single-defined-constant-globally iterate)
    (block 
      (script-comment "`instantiate-existential' at (0 1 0 0)")
      (instantiate-theorem undefined-for-negative ("m" "x" "f"))
      simplify))))

(comment
 (def-theorem raise-in-bound%place-when-defined
   "forall(sigma:istate, p:place, f:[place -> place],
        #(raise(sigma,f)(p)) implies 
	raise(sigma,f)(p) in bound%place(sigma))"
   (theory places)
   (proof
    (
     (unfold-single-defined-constant-globally raise)
     (apply-macete-with-minor-premises tr%first%entry-in-set))))

 (def-theorem raise-id-on-bound%place
   "forall(f:[place,place],p:place,sigma:istate,
    p in bound%place(sigma)
     implies 
    raise(sigma,f)(p)=p);"
   (theory places)
   (proof
    (
     (unfold-single-defined-constant-globally raise)
     (apply-macete-with-minor-premises bound%place-characterization)
     (apply-macete-with-minor-premises tr%first%entry-equation)
     simplify))))

(def-constant a%copy
  "lambda(gamma_0: [place -> word], f:[place -> place],
     if(copy%fn(gamma_0, f),
	copy(gamma_0,f),
	?[place -> word]))"
  (theory places))

(def-constant c%copy%fn
  "lambda(sigma:istate,f:[place -> place],
     forall(p:place, p in bound%place (sigma) implies f(p)==default(sigma)(p)))"
  (theory places))

(def-constant c%copy
  "lambda(sigma:istate,f:[place,place],
     if(c%copy%fn(sigma,f), 
	make%istate(gamma(sigma),f),
	?istate))"
  (theory places))

(def-theorem copy-safety
  "forall(f:[place,place],sigma:istate,
   #(c%copy(sigma,f)) implies 
   abstr(c%copy(sigma,f)) = a%copy(abstr(sigma),raise(sigma,f)))"
  (theory places)
  (proof
   (


    (unfold-single-defined-constant-globally c%copy)
    (unfold-single-defined-constant-globally c%copy%fn)
    (unfold-single-defined-constant-globally a%copy)
    (unfold-single-defined-constant-globally copy%fn)
    simplify-insistently
    direct-inference
    (instantiate-theorem default-modification-lemma ("f" "sigma"))
    (move-to-ancestor 5)
    (move-to-descendent (1 0))
    (block 
     (script-comment "`instantiate-theorem' at (0 1 0)")
     (incorporate-antecedent "copy%fn(with(f:[place,word],f),with(f:[place,place],f));")
     (unfold-single-defined-constant-globally copy%fn)
     simplify-insistently)
    (move-to-ancestor 1)
    direct-and-antecedent-inference-strategy
    (move-to-ancestor 1)
    direct-and-antecedent-inference-strategy
    (move-to-ancestor 4)
    (block 
     (script-comment "`direct-and-antecedent-inference-strategy' at (0)")
     (auto-instantiate-universal-antecedent "with(f:[place,place],sigma:istate,
  forall(p:place,
    p in bound%place(sigma) implies 
    f(p)==default(sigma)(p)));")
     (antecedent-inference "with(p:prop,p or p);"))

    )))

(comment
 (def-theorem copy-safety-corollary
  "forall(f:[place,place],sigma:istate,
   #(c%copy(sigma,f)) 
      implies
   #(a%copy(abstr(sigma),raise(sigma,f))))"
  (theory places)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (instantiate-theorem copy-safety ("f" "sigma"))
    ))))

(def-constant lower
  "lambda(sigma:istate,f:[place,place],
     lambda(p:place, if (p in bound%place(sigma), default(sigma)(p), f(p))))"
  (theory places))

(def-theorem raise-lower-composition
  "forall(f:[place,place],sigma:istate,
    #(a%copy(abstr(sigma),f)) implies f=raise(sigma, lower(sigma, f)))"
  (theory places)
  (proof
   (


    (unfold-single-defined-constant-globally a%copy)
    (unfold-single-defined-constant-globally lower)
    (unfold-single-defined-constant-globally copy%fn)
    simplify
    simplify-insistently
    direct-and-antecedent-inference-strategy
    (unfold-single-defined-constant-globally raise)
    extensionality
    simplify
    direct-and-antecedent-inference-strategy
    (case-split ("x_0 in bound%place(sigma)"))
    (block 
     (script-comment "`case-split' at (1)")
     (apply-macete-with-minor-premises tr%first%entry-identity-in-set)
     (backchain "with(p:place,w:word,forall(x:place,#(w) implies p=x));")
     (apply-macete-with-minor-premises rev%bound%place-abstr-definedness))
    (block 
     (script-comment "`case-split' at (2)")
     (apply-macete-with-minor-premises tr%first%entry-equation)
     simplify
     (case-split ("#(f(x_0))"))
     (block 
      (script-comment "`case-split' at (1)")
      (instantiate-universal-antecedent "with(w:word,p:prop,
  forall(x_$0:place,forsome(x:place,p) implies #(w)));"
					("f(x_0)"))
      (instantiate-universal-antecedent "with(p:prop,forall(x_$1:place,not(p)));"
					("x_0"))
      (block 
       (script-comment "`instantiate-universal-antecedent' at (0 0 1)")
       (incorporate-antecedent "with(w:word,#(w));")
       (apply-macete-with-minor-premises rev%bound%place-abstr-definedness)
       (apply-macete-with-minor-premises tr%first%entry-identity-in-set)))
     insistent-direct-and-antecedent-inference-strategy)
    )))


(def-theorem copy-liveness 
  "forall(f:[place,place],sigma:istate,
    #(a%copy(abstr(sigma),f)) implies
      abstr(c%copy(sigma, lower(sigma, f)))= a%copy(abstr(sigma),f))"
  reverse
  (theory places)
  (proof
   (

    
    (unfold-single-defined-constant-globally a%copy)
    (unfold-single-defined-constant-globally c%copy)
    (unfold-single-defined-constant-globally c%copy%fn)
    (unfold-single-defined-constant-globally lower)
    (unfold-single-defined-constant-globally copy%fn)
    simplify-insistently
    direct-and-antecedent-inference-strategy
    (force-substitution "f"
			"raise(sigma,
         lambda(p:place,
           if(p in bound%place(sigma),
             default(sigma)(p),
             f(p))))"
			(1))
    (block 
     (script-comment "`force-substitution' at (0)")
     (instantiate-theorem default-modification-lemma
			  ("lambda(p:place,
                      if(p in bound%place(sigma),
                        default(sigma)(p),
                        f(p)))" "sigma"))
     (move-to-ancestor 1)
     (contrapose "with(p:prop,not(p));")
     simplify)
    (block 
     (script-comment "`force-substitution' at (1)")
     (cut-with-single-formula "f=raise(sigma,lower(sigma,f))")
     (block 
      (script-comment "`cut-with-single-formula' at (0)")
      (incorporate-antecedent "with(f:[place,place],f=f);")
      (unfold-single-defined-constant-globally lower))
     (block 
      (script-comment "`cut-with-single-formula' at (1)")
      (apply-macete-with-minor-premises raise-lower-composition)
      (unfold-single-defined-constant-globally a%copy)
      (unfold-single-defined-constant-globally copy%fn)
      simplify))


    )))

(def-theorem copy-liveness-corollary
  "forall(f:[place,place],sigma:istate,
    #(a%copy(abstr(sigma),f)) 
       implies 
    #(c%copy(sigma, lower(sigma, f))))"
  (theory places)
  (proof
   (

    direct-and-antecedent-inference-strategy
    (instantiate-theorem copy-liveness ("f" "sigma"))
    )))


(def-constant c%redirect%fn
  "lambda(f:[place -> place],sigma:istate,
     ran{f} inters dom{gamma(sigma)}=empty_indic{place}
      and 
     dom{f} inters ran{f}=empty_indic{place}
      and 
     forall(x:place,
       x in dom{f}
        implies 
       default(sigma)(x)=default(sigma)(f(x))))"
  (theory places))
   
(def-constant c%redirect
  "lambda(sigma:istate,f: [place -> place],
       if(c%redirect%fn(f, sigma),
           make%istate(gamma(sigma),
                       lambda(x:place,
                         if(x in dom{f},
                           f(x),
                           default(sigma)(x)))),
           ?istate))"
   (theory places))


(def-theorem c%redirect-no-op
  "forall(f:[place,place],sigma:istate,
    #(c%redirect(sigma,f))
      implies 
    abstr(c%redirect(sigma,f))=abstr(sigma))"
  (theory places)
  (proof
   (

    (unfold-single-defined-constant-globally c%redirect)
    (unfold-single-defined-constant-globally c%redirect%fn)
    simplify
    (apply-macete-with-minor-premises tr%rev%domain-membership-iff-defined)
    (apply-macete-with-minor-premises default-multiplicity-reduction)
    simplify

    )))

(def-constant user%eq
  "lambda(f,g:[place -> word], u:sets[place],
     restrict(f,u)=restrict(g,u))"
   (theory places))

(def-constant c%shadow
  "lambda(sigma:istate, f:[place -> place],
     if(#(a%copy(abstr(sigma),f)),
        c%copy(sigma, lower(sigma, f)),
        ?istate))"
  (theory places))


(def-constant shadow%set
  "lambda(sigma:istate, f:[place -> place], 
       dom{f} inters (bound%place(sigma)^^))"
  (theory places))


(def-theorem c%shadow-no-op
  "forall(f:[place -> place], v:sets[place], sigma:istate, 
      v disj shadow%set(sigma,f) and #(c%shadow(sigma,f))
        implies 
      user%eq(abstr(sigma),abstr(c%shadow(sigma,f)), v))"
  (theory places)
  (proof
   (


    (unfold-single-defined-constant-globally user%eq)
    (unfold-single-defined-constant-globally c%shadow)
    simplify
    (apply-macete-with-minor-premises copy-liveness)
    (unfold-single-defined-constant-globally shadow%set)
    simplify-insistently
    direct-and-antecedent-inference-strategy
    extensionality
    simplify-insistently
    direct-and-antecedent-inference-strategy
    (instantiate-universal-antecedent "with(p:prop,forall(x:place,p));" ("x_0"))
    (block 
     (script-comment "`instantiate-universal-antecedent' at (0 0 1 0)")
     (incorporate-antecedent "with(f:[place,word],#(f));")
     (unfold-single-defined-constant-globally a%copy)
     simplify
     (unfold-single-defined-constant-globally copy)
     simplify
     direct-and-antecedent-inference-strategy
     insistent-direct-inference
     (antecedent-inference "with(p:prop,p or p);")
     (contrapose "with(p:prop,not(p));")
     (incorporate-antecedent "copy%fn(with(f:[place,word],f),with(f:[place,place],f));")
     (unfold-single-defined-constant-globally copy%fn)
     simplify)
    (block 
     (script-comment "`instantiate-universal-antecedent' at (0 0 1 1)")
     (incorporate-antecedent "with(f:[place,word],#(f));")
     (unfold-single-defined-constant-globally a%copy)
     simplify
     (unfold-single-defined-constant-globally copy)
     direct-and-antecedent-inference-strategy
     (unfold-single-defined-constant-globally abstr)
     (incorporate-antecedent "copy%fn(with(f:[place,word],f),with(f:[place,place],f));")
     (unfold-single-defined-constant-globally copy%fn)
     simplify
     direct-and-antecedent-inference-strategy
     (incorporate-antecedent "with(x_0:place,sigma:istate,x_0 in bound%place(sigma));")
     (unfold-single-defined-constant-globally bound%place)
     simplify
     (incorporate-antecedent "with(p:place,w:word,forall(x:place,#(w) implies p=x));")
     (unfold-single-defined-constant-globally abstr)
     simplify)

    )))

(def-constant c%fill
  "lambda(sigma:istate, a:sets[place], 
      if(dom{gamma(sigma)} subseteq a,
         ifill(sigma,a),
         ?istate))"
  (theory places))


(def-theorem c%fill-no-op
  "forall(sigma:istate, a:sets[place],
      #(c%fill(sigma,a)) 
        implies 
      abstr(sigma)=abstr(c%fill(sigma,a)))"
  (theory places)
  (proof
   (

 
    (unfold-single-defined-constant-globally c%fill)
    simplify
    (apply-macete-with-minor-premises ifill-abstraction)
    simplify)))


(def-theorem bound%place%stability
  "forall(h:[place,place],x:place,sigma:istate,
    x in bound%place(sigma) and #(c%copy(sigma,h))
      implies 
     x in bound%place(c%copy(sigma,h)))"
  (theory places)
  (proof
   (


    direct-and-antecedent-inference-strategy
    (cut-with-single-formula " bound%place(sigma) subseteq bound%place(c%copy(sigma,h))")
    simplify
    (block 
     (script-comment "`cut-with-single-formula' at (1)")
     (apply-macete-with-minor-premises bound%place%monotonicty)
     (incorporate-antecedent "with(f:istate,#(f));")
     (unfold-single-defined-constant-globally c%copy)
     simplify
     (unfold-single-defined-constant-globally c%copy%fn)
     simplify)

    )))