(include-files
  (files (imps theory-inference/general-macetes-supplements)
	 (imps theories/networks/filter-rules)
	 ))

(def-constant independent%rules
  "lambda(r_1,r_2:filter%rules,
     forall(d:datagrams, b:directions, s:filtered%states,
       not(check%fr%condition(r_1,d,b,s))
        or
       not(check%fr%condition(r_2,d,b,s))))"
  (theory single-filter-theory))

(def-theorem independent%rules-independent-condition
  "forall(r_1,r_2:filter%rules,
     (not(fr%direction(r_1) = fr%direction(r_2))
       or
      fr%source%addresses(r_1) disj fr%source%addresses(r_2)
       or
      fr%destination%addresses(r_1) disj fr%destination%addresses(r_2)
       or 
      fr%protocols(r_1) disj fr%protocols(r_2)
       or 
      fr%source%ports(r_1) disj fr%source%ports(r_2)
       or
      fr%destination%ports(r_1) disj fr%destination%ports(r_2)
       or
      forall(s:filtered%states, d:datagrams,
        not(is%true(fr%state%condition(r_1)(s,d)))
         and
        not(is%true(fr%state%condition(r_2)(s,d)))))
       implies
      independent%rules(r_1,r_2))"
  (theory single-filter-theory)
  (proof
   (

    direct-inference
    direct-inference
    (unfold-single-defined-constant-globally independent%rules)
    (unfold-single-defined-constant-globally check%fr%condition)
    direct-inference
    (antecedent-inference "with(p:prop,p);")
    simplify
    (block 
      (script-comment "`antecedent-inference' at (1)")
      (instantiate-universal-antecedent "with(p:prop,p);"
					("source%address(d)"))
      simplify
      simplify)
    (block 
      (script-comment "`antecedent-inference' at (2)")
      (instantiate-universal-antecedent 
       "with(p:prop,p);"
       ("destination%address(d)"))
      simplify
      simplify)
    (block 
      (script-comment "`antecedent-inference' at (3)")
      (instantiate-universal-antecedent 
       "with(p:prop,p);" 
       ("protocol(d)"))
      simplify
      simplify)
    (block 
      (script-comment "`antecedent-inference' at (4)")
      (instantiate-universal-antecedent 
       "with(p:prop,p);" 
       ("source%port(d)"))
      simplify
      simplify)
    (block 
      (script-comment "`antecedent-inference' at (5)")
      (instantiate-universal-antecedent 
       "with(p:prop,p);"
       ("destination%port(d)"))
      simplify
      simplify)
    (block 
      (script-comment "`antecedent-inference' at (6)")
      (instantiate-universal-antecedent "with(p:prop,p);" ("s" "d"))
      simplify)
    
    )))

(def-theorem independent%rules-dependent-condition
  "forall(r_1,r_2:filter%rules,
     fr%direction(r_1) = fr%direction(r_2)
      and
     not(fr%source%addresses(r_1) disj fr%source%addresses(r_2))
      and
     not(fr%destination%addresses(r_1) disj fr%destination%addresses(r_2))
      and 
     not(fr%protocols(r_1) disj fr%protocols(r_2))
      and 
     not(fr%source%ports(r_1) disj fr%source%ports(r_2))
      and
     not(fr%destination%ports(r_1) disj fr%destination%ports(r_2))
      and
     fr%state%condition(r_1) = null%state%condition
      and
     fr%state%condition(r_2) = null%state%condition
      implies 
     not(independent%rules(r_1,r_2)))"
  (theory single-filter-theory)
  (proof
   (

    simplify
    direct-and-antecedent-inference-strategy
    (unfold-single-defined-constant-globally independent%rules)
    (unfold-single-defined-constant-globally check%fr%condition)
    simplify
    (instantiate-existential 
     ("with(z:data, 
         make%datagram(x,x_$1,x_$2,x_$0,x_$3,empty_indic{tcp%flags},z))"))
    (move-to-ancestor 1)
    (unfold-single-defined-constant-globally initiates%tcp%connection)
    simplify

    )))


