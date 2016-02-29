(include-files
 (files  (imps theories/vmach/places)))

(def-language language-for-memory-objects
  (embedded-language  h-o-real-arithmetic)
  (base-types mem%obj word page))

(def-theory memory-objects
  (language language-for-memory-objects)
  (component-theories h-o-real-arithmetic))


(def-cartesian-product place
  ("mem%obj" "nn")
  (theory memory-objects)
  (constructor make%place)
  (accessors mem index))

(def-cartesian-product istate
  ("[place -> word]" "[place -> place]")
  (theory memory-objects)
  (constructor make%istate)
  (accessors gamma default))

(def-theorem ()
  "forall(x:sets[[place,word],[place,place]],
   #(x,istate)
    iff 
   forsome(%y_0:[place,word],%y_1:[place,place],
     x
     =lambda(%x_0:[place,word],%x_1:[place,place],
        if(%y_0=%x_0 and %y_1=%x_1,
          an%individual,
          ?unit%sort))))"
  (theory  memory-objects)
  (proof
   (


    (apply-macete-with-minor-premises istate-defining-axiom_memory-objects)
    simplify
    )))


(def-translation places-to-memory
  (source places)
  (target memory-objects)
  (fixed-theories h-o-real-arithmetic)
  (sort-pairs (place place) (istate istate))
  (constant-pairs (gamma gamma) (default default) (make%istate make%istate))
  (theory-interpretation-check using-simplification))

(def-renamer places-to-memory-renamer
  (pairs
   (abstr abstr)
   (promote promote)
   (raise raise)
   (bound%place bound%place)
   (istore istore)
   (copy copy)
   (regular%place regular%place)
   (ifill ifill)))

(def-transported-symbols (abstr bound%place copy promote raise istore regular%place ifill)
  (translation places-to-memory)
  (renamer places-to-memory-renamer))


(def-constant make%gamma
  "lambda(g:[mem%obj, nn -> word],
      lambda(p:place,g(mem(p), index(p))))"
  (theory  memory-objects))

(def-constant make%default
  "lambda(f:[mem%obj ->mem%obj], o:[mem%obj ->nn],
      lambda(p:place,  make%place(f(mem(p)), index(p)+o(mem(p)))))"
  (theory  memory-objects))


(def-constant make%istate_p
  "lambda(g:[mem%obj, nn -> word], f:[mem%obj ->mem%obj], o:[mem%obj ->nn],
     make%istate(make%gamma(g), make%default(f,o)))"
  (theory  memory-objects))

(def-overloading make%istate
  (memory-objects make%istate)
  (memory-objects make%istate_p)
  (places  make%istate))

(def-constant abstr_p
  "lambda(sigma:istate, lambda(m:mem%obj, i:nn, abstr(sigma)(make%place(m,i))))"
  (theory  memory-objects))

(comment
 (def-constant simple%fibred%map
  "lambda(m,m_1:mem%obj, offset:nn, s:sets[place],
       lambda(p:place, 
         if(p in s, p, mem(p)=m, make%place(m_1,index(p)+offset), ?place)))"
  (theory  memory-objects)))

(def-constant twist
  "lambda(f:[mem%obj->mem%obj], offset:[mem%obj->nn],
       lambda(p:place, 
         make%place(f(mem(p)),index(p)+offset(mem(p)))))"
  (theory  memory-objects))

(def-constant bound%mem
  "lambda(s:istate, indic{m:mem%obj, forsome(p:place, mem(p)=m)})"
  (theory  memory-objects))

(def-theorem raise-condition-corollary
  "forall(f:[place,place],sigma:istate, 
    forall(x:place,  #(f(f(x))) implies 
                    (x in bound%place(sigma) or f(x) in bound%place(sigma) or
                   f(f(x)) in bound%place(sigma))) 
 
     implies
    raise(sigma, f)= 
    lambda(x:place, if(x in bound%place(sigma), x, f(x) in bound%place(sigma), f(x), f oo f(x))))"

  (theory places)
  (usages transportable-macete)
  (proof
   (

    (apply-macete-with-minor-premises raise-condition)
    direct-and-antecedent-inference-strategy
    simplify

    )))


(def-theorem raise-condition-variant
  "forall(m_1, m_2:mem%obj, s:istate, f:[mem%obj->mem%obj],offset:[mem%obj->nn],
    forall(x:place,  #(twist(f,offset)(twist(f,offset)(x))) implies 
                    (x in bound%place(s) or mem(x)=m_1 or mem(x)=m_2))
     and
    forall(x:place, mem(x)=m_1 and #(twist(f,offset)(x)) implies twist(f,offset)(x) in bound%place(s))
    and
    f(m_2)=m_1
     implies
    raise(s, twist(f,offset))= 
    lambda(x:place, if(x in bound%place(s), x, twist(f,offset)(x) in bound%place(s), twist(f,offset)(x), twist(f,offset) oo (twist(f,offset))(x))))"
  
  (theory memory-objects)
  (proof
   (


    (apply-macete-with-minor-premises tr%raise-condition-corollary)
    (move-to-sibling 2)
    (unfold-single-defined-constant (0) twist)
    (block 
     (script-comment "`apply-macete-with-minor-premises' at (1)")
     direct-and-antecedent-inference-strategy
     (antecedent-inference "with(p:prop,p and p and p);")
     (backchain "with(p:prop,
  forall(x:place,
    p and p implies 
    with(f:place,f) in with(f:sets[place],f)));")
     direct-and-antecedent-inference-strategy
     (contrapose "with(x:place,f:[place,place],s:istate,
  not(f(x) in bound%place(s)));")
     (backchain "with(p:prop,
  forall(x:place,
    p and p implies 
    with(f:place,f) in with(f:sets[place],f)));")
     direct-and-antecedent-inference-strategy
     (auto-instantiate-universal-antecedent "with(m_2,m_1:mem%obj,s:istate,offset:[mem%obj,nn],f:[mem%obj,mem%obj],
  forall(x:place,
    #(twist(f,offset)(twist(f,offset)(x)))
     implies 
    (x in bound%place(s) or mem(x)=m_1 or mem(x)=m_2)));")
     (contrapose "with(m_1,m:mem%obj,not(m=m_1));")
     (unfold-single-defined-constant (0) twist)
     simplify
     (apply-macete-with-minor-premises mem%make-place)
     simplify
     (cut-with-single-formula "#(offset(m_2))")
     simplify
     (block 
      (script-comment "`cut-with-single-formula' at (1)")
      (cut-with-single-formula "#(twist(f,offset)(x))")
      (incorporate-antecedent "with(x:place,offset:[mem%obj,nn],f:[mem%obj,mem%obj],
  #(twist(f,offset)(x)));")
      (unfold-single-defined-constant (0) twist)
      simplify))

    )))

(def-theorem raise-condition-variant-1
  "forall(m_1, m_2:mem%obj, s:istate, f:[mem%obj->mem%obj],offset:[mem%obj->nn],
    forall(x:place,  #(twist(f,offset)(x)) implies 
                    (x in bound%place(s) or mem(x)=m_1 or mem(x)=m_2))
     and
    forall(x:place, mem(x)=m_1 and #(twist(f,offset)(x)) implies twist(f,offset)(x) in bound%place(s))
    and
    f(m_2)=m_1
    and
    not m_1 in bound%mem(s)
     implies
    raise(s, twist(f,offset))= 
    lambda(x:place, if(x in bound%place(s), x, mem(x)=m_1, twist(f,offset)(x),  mem(x)=m_2, twist(f,offset) oo (twist(f,offset))(x), ?place)))"
  
  (theory memory-objects)
  (proof
   (

    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises raise-condition-variant)
    extensionality
    simplify
    direct-and-antecedent-inference-strategy
    (case-split ("mem(x_0)=m_1"))
    (block 
     (script-comment "`case-split' at (1)")
     simplify
     (case-split ("#(twist(f,offset)(x_0))"))
     (block 
      (script-comment "`case-split' at (1)")
      simplify
      (instantiate-universal-antecedent "with(p:prop,
  forall(x:place,
    p and p implies 
    with(f:place,f) in with(f:sets[place],f)));"
					("x_0"))
      simplify)
     (block 
      (script-comment "`case-split' at (2)")
      simplify
      insistent-direct-inference
      (antecedent-inference "with(p:prop,p or p);")))
    simplify
    direct-and-antecedent-inference-strategy
    (block 
     (script-comment "`direct-and-antecedent-inference-strategy' at (0)")
     (cut-with-single-formula "not twist(f,offset)(x_0) in bound%place(s)")
     simplify
     (block 
      (script-comment "`cut-with-single-formula' at (1)")
      (unfold-single-defined-constant (0) twist)
      simplify
      (incorporate-antecedent "with(m_1:mem%obj,f:sets[mem%obj],not(m_1 in f));")
      (unfold-single-defined-constant (0) bound%mem)
      simplify-insistently
      direct-and-antecedent-inference-strategy
      (contrapose "with(p:prop,forall(p:place,with(p:prop,not(p))));")
      (instantiate-existential ("make%place(m_1,offset(m_2)+index(x_0))"))
      simplify))
    simplify
    (instantiate-universal-antecedent "with(p:prop,f:place,
  forall(x:place,#(f) implies (p or p or p)));"
				      ("x_0"))
    simplify

    )))

(comment
 (def-overloading abstr
  (memory-objects abstr)
  (memory-objects abstr_p)
  (places abstr)))