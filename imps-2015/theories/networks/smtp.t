(include-files
  (files (imps theories/networks/single-filter-policy)))

(def-constant smtp%connection
  "lambda(s_1:states,s_2:filtered%states,f:[nn -> nn],
          a_1,a_2:addresses,p_1,p_2:ports,
     tcp%connection(s_1,s_2,f,a_1,a_2,p_1,p_2)
      and 
     (p_1 > 1023 and p_2 = 25))"
  (theory single-filter-theory))

(def-constant only%smtp%connections
  "forall(s_1:states,s_2:filtered%states,f:[nn -> nn],
          a_1,a_2:addresses,p_1,p_2:ports,
    tcp%connection(s_1,s_2,f,a_1,a_2,p_1,p_2) 
     implies 
    smtp%connection(s_1,s_2,f,a_1,a_2,p_1,p_2))"
  (theory single-filter-theory))

(def-constant no%smtp%connections
  "forall(s_1:states,s_2:filtered%states,f:[nn -> nn],
          a_1,a_2:addresses,p_1,p_2:ports,
    tcp%connection(s_1,s_2,f,a_1,a_2,p_1,p_2) 
     implies 
    not(smtp%connection(s_1,s_2,f,a_1,a_2,p_1,p_2)))"
  (theory single-filter-theory))

(def-constant limited%smtp%connections
  "lambda(senders,receivers:sets[addresses],
     forall(s_1:states,s_2:filtered%states,f:[nn -> nn],
            a_1,a_2:addresses,p_1,p_2:ports,
       smtp%connection(s_1,s_2,f,a_1,a_2,p_1,p_2)
        and
       senders subseteq internal
        and
       receivers subseteq internal
        implies
       (a_1 in external implies a_2 in receivers)
        and
       (a_2 in external implies a_1 in senders)))"
  (theory single-filter-theory))

(def-constant smtp%filter%condition%1
  "lambda(d:datagrams, b:directions, senders,receivers:sets[addresses],
     filter%condition(d,b,
                      inbound,
                      external,
                      receivers,
                      tcp,
                      lambda(p:ports, p > 1023),
                      lambda(p:ports, p = 25),
                      truth))"
  (theory single-filter-theory))

(def-constant smtp%filter%condition%2
  "lambda(d:datagrams, b:directions, senders,receivers:sets[addresses],
     filter%condition(d,b,
                      outbound,
                      receivers,
                      external,
                      tcp,
                      lambda(p:ports, p = 25),
                      lambda(p:ports, p > 1023),
                      falsehood))"
  (theory single-filter-theory))

(def-constant smtp%filter%condition%3
  "lambda(d:datagrams, b:directions, senders,receivers:sets[addresses],
     filter%condition(d,b,
                      outbound,
                      senders,
                      external,
                      tcp,
                      lambda(p:ports, p > 1023),
                      lambda(p:ports, p = 25),
                      truth))"
  (theory single-filter-theory))

(def-constant smtp%filter%condition%4
  "lambda(d:datagrams, b:directions, senders,receivers:sets[addresses],
     filter%condition(d,b,
                      inbound,
                      external,
                      senders,
                      tcp,
                      lambda(p:ports, p = 25),
                      lambda(p:ports, p > 1023),
                      falsehood))"
  (theory single-filter-theory))

(def-constant smtp%filter%specification
  "lambda(senders,receivers:sets[addresses],
     forall(d:datagrams,b:directions,s:filtered%states,
       if(smtp%filter%condition%1(d,b,senders,receivers), filter(d,b,s),
          smtp%filter%condition%2(d,b,senders,receivers), filter(d,b,s),
          smtp%filter%condition%3(d,b,senders,receivers), filter(d,b,s),
          smtp%filter%condition%4(d,b,senders,receivers), filter(d,b,s),
          not(filter(d,b,s)))))"
  (theory single-filter-theory))
        
(def-theorem smtp-filter-correctness-1
  "forall(senders,receivers:sets[addresses],
     smtp%filter%specification(senders,receivers)
      implies 
     only%smtp%connections)"
  (theory single-filter-theory)
  (proof
   (

    unfold-defined-constants
    (unfold-single-defined-constant-globally smtp%connection)
    direct-inference
    direct-inference
    direct-inference
    direct-inference
    direct-inference
    (instantiate-theorem 
     first-datagram-in-tcp_connection-lemma
     ("s_1" "s_2" "f" "a_1" "a_2" "p_1" "p_2"))
    (instantiate-theorem 
     tcp_connection-embedding-lemma
     ("s_1" "s_2" "f" "a_1" "a_2" "p_1" "p_2" "0"))
    (instantiate-theorem 
     filtered_states-defining-axiom-lemma 
     ("s_2" "f(0)"))
    (incorporate-antecedent 
     "with(p_2,p_1:ports,a_2,a_1:addresses,f:datagrams,
          has%profile(f,a_1,a_2,p_1,p_2,tcp));")
    (unfold-single-defined-constant-globally has%profile)
    direct-inference
    (instantiate-universal-antecedent 
     "with(p:prop,
        forall(d:datagrams,b:directions,s:filtered%states,p));"
     ("s_2(f(0))" "b" "takefirst{s_2,f(0)}"))
    (block 
      (script-comment "`instantiate-universal-antecedent' at (0 0)")
      (incorporate-antecedent "with(p:prop,if(p, p, p));")
      simplify
      (backchain-backwards "with(p:prop,p and p and p and p and p);")
      (backchain-backwards "with(p:prop,p and p and p and p and p);")
      (force-substitution "s_2(f(0))" "s_1(0)" (0 1 2 3))
      (weaken (4 3 2 0))
      (unfold-single-defined-constant-globally smtp%filter%condition%1)
      (unfold-single-defined-constant-globally smtp%filter%condition%2)
      (unfold-single-defined-constant-globally smtp%filter%condition%3)
      (unfold-single-defined-constant-globally smtp%filter%condition%4)
      (unfold-single-defined-constant-globally filter%condition)
      simplify)
    (apply-macete-with-minor-premises 
     filtered_states-are-closed-under-takefirst)

    )))

(def-theorem smtp-filter-correctness-2
  "forall(senders,receivers:sets[addresses],
     smtp%filter%specification(senders,receivers)
      implies 
     limited%smtp%connections(senders,receivers))"
  (theory single-filter-theory)
  (proof
   (

    unfold-defined-constants
    (unfold-single-defined-constant-globally smtp%connection)
    direct-inference
    direct-inference
    direct-inference
    direct-inference
    (instantiate-theorem 
     first-datagram-in-tcp_connection-lemma
     ("s_1" "s_2" "f" "a_1" "a_2" "p_1" "p_2"))
    (instantiate-theorem 
     tcp_connection-embedding-lemma
     ("s_1" "s_2" "f" "a_1" "a_2" "p_1" "p_2" "0"))
    (instantiate-theorem 
     filtered_states-defining-axiom-lemma 
     ("s_2" "f(0)"))
    (incorporate-antecedent 
     "with(p_2,p_1:ports,a_2,a_1:addresses,f:datagrams,
        has%profile(f,a_1,a_2,p_1,p_2,tcp));")
    (unfold-single-defined-constant-globally has%profile)
    direct-inference
    (instantiate-universal-antecedent 
     "with(p:prop,
        forall(d:datagrams,b:directions,s:filtered%states,p));"
     ("s_2(f(0))" "b" "takefirst{s_2,f(0)}"))
    (block 
      (script-comment "`instantiate-universal-antecedent' at (0 0)")
      (incorporate-antecedent "with(p:prop,if(p, p, p));")
      simplify
      (force-substitution "a_1" "source%address(s_1(0))" (0 1))
      (force-substitution "a_2" "destination%address(s_1(0))" (0 1))
      (force-substitution "s_2(f(0))" "s_1(0)" (0 1 2 3))
      (weaken (3 2 0))
      (unfold-single-defined-constant-globally smtp%filter%condition%1)
      (unfold-single-defined-constant-globally smtp%filter%condition%2)
      (unfold-single-defined-constant-globally smtp%filter%condition%3)
      (unfold-single-defined-constant-globally smtp%filter%condition%4)
      (unfold-single-defined-constant-globally filter%condition)
      simplify
      (antecedent-inference "with(p:prop,p and p and p);")
      direct-and-antecedent-inference-strategy
      (block 
	(script-comment 
	 "`direct-and-antecedent-inference-strategy' at (0 0 0 1 0)")
	(instantiate-theorem 
	 external-and-internal-are-disjoint
	 ("source%address(s_1(0))"))
	(instantiate-universal-antecedent 
	 "with(senders:sets[addresses],senders subseteq internal);"
	 ("source%address(s_1(0))")))
      (block 
	(script-comment 
	 "`direct-and-antecedent-inference-strategy' at (0 1 0 1 0 0)")
	(instantiate-theorem 
	 external-and-internal-are-disjoint
	 ("destination%address(s_1(0))"))
	(instantiate-universal-antecedent 
	 "with(receivers:sets[addresses],receivers subseteq internal);"
	 ("destination%address(s_1(0))"))))
    (apply-macete-with-minor-premises 
     filtered_states-are-closed-under-takefirst)

    )))

(def-theorem smtp-filter-correctness-3
  "forall(senders,receivers:sets[addresses],
     smtp%filter%specification(senders,receivers)
      and
     receivers subseteq internal
      implies 
     limited%externally%initiated%tcp%connections(receivers))"
  (theory single-filter-theory)
  (proof
   (

    unfold-defined-constants
    direct-and-antecedent-inference-strategy
    (instantiate-universal-antecedent 
     "with(p:prop,
        forall(d:datagrams,b:directions,s:filtered%states,p));"
     ("d" "inbound" "s"))
    (incorporate-antecedent "with(p:prop,if(p, p, p));")
    simplify
    (unfold-single-defined-constant-globally smtp%filter%condition%1)
    (unfold-single-defined-constant-globally smtp%filter%condition%2)
    (unfold-single-defined-constant-globally smtp%filter%condition%3)
    (unfold-single-defined-constant-globally smtp%filter%condition%4)
    (unfold-single-defined-constant-globally filter%condition)
    direct-and-antecedent-inference-strategy
    (weaken (9 7 5 4 3 2 0))
    (incorporate-antecedent 
     "with(d:datagrams,receivers:sets[addresses],
        destination%address(d) in internal diff receivers);")
    simplify-insistently

    )))