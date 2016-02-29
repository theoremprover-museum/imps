(include-files
  (files (imps theories/networks/states)
	 (imps theories/networks/address-applications)))

;(set (proof-log-port) (standard-output))

(def-language single-filter-language
  (embedded-languages datagrams)
  (base-types directions)
  (constants
   (external "sets[addresses]")
   (internal "sets[addresses]")
   (inbound directions)
   (outbound directions)
   (filter "[datagrams,directions,states -> prop]")
   ))

(def-theory single-filter-theory
  (language single-filter-language)
  (component-theories datagrams)
  (distinct-constants (inbound outbound))
  (axioms
   (external-and-internal-are-disjoint
    "external disj internal")
   (every-direction-is-inbound-or-outbound
    "forall(b:directions, b = inbound or b = outbound)")
   ))

(def-constant opposite%direction
  "lambda(b:directions, if(b = inbound, outbound, inbound))"
  (theory single-filter-theory))

(def-theorem opposite_direction-is-total
  "total_q{opposite%direction,[directions -> directions]}"
  (usages d-r-convergence)
  (theory single-filter-theory)
  (proof
   (

    (unfold-single-defined-constant (0) opposite%direction)
    simplify-insistently

    )))

(def-theorem reverse-filter-obligation-1
  "internal disj external"
  (theory single-filter-theory)
  (proof
   (

    (assume-theorem external-and-internal-are-disjoint)
    (incorporate-antecedent "with(p:prop,p);")
    simplify-insistently

    )))

(def-theorem reverse-filter-obligation-2
  "forall(b:directions,b = outbound or b = inbound)"
  (theory single-filter-theory)
  (proof
   (

    direct-inference
    (instantiate-theorem every-direction-is-inbound-or-outbound ("b"))
    simplify
    simplify

    )))

(def-translation reverse-filter
  (source single-filter-theory)
  (target single-filter-theory)
  (fixed-theories datagrams)
  (constant-pairs
   (external internal)
   (internal external)
   (inbound outbound)
   (outbound inbound))
  (theory-interpretation-check using-simplification))

(def-theorem filtered-states-exist
  "forsome(x:states,
     forall(n:nn,
       #(x(n))
        implies 
       forsome(b:directions, filter(x(n),b,takefirst{x,n}))))"
  (theory single-filter-theory)
  (proof
   (

    (instantiate-existential ("empty%state"))
    (block 
      (script-comment "`instantiate-existential' at (0 0 0)")
      (instantiate-existential ("inbound"))
      (contrapose "with(p:prop,p);")
      (unfold-single-defined-constant-globally empty%state))
    (apply-macete-with-minor-premises empty_state-is-a-state)

    )))

(def-atomic-sort filtered%states
  "lambda(s:states, 
     forall(n:nn, 
       #(s(n)) 
        implies 
       forsome(b:directions,filter(s(n),b,takefirst{s,n}))))"
  (theory single-filter-theory))

(def-theorem filtered_states-defining-axiom-lemma
  "forall(s:filtered%states,n:nn,
     #(s(n)) 
      implies 
     forsome(b:directions,filter(s(n),b,takefirst{s,n})))"
  (theory single-filter-theory)
  (proof
   (

    direct-and-antecedent-inference-strategy
    (instantiate-theorem 
     filtered%states-defining-axiom_single-filter-theory ("s"))
    (block 
      (script-comment "`instantiate-theorem' at (0 0)")
      (beta-reduce-antecedent 
       "with(s:filtered%states,
          lambda(s:states,
            forall(n:nn,
              #(s(n))
               implies 
              forsome(b:directions,filter(s(n),b,takefirst{s,n}))))
          (s));")
      (backchain "with(p:prop,forall(n_$0:nn,p));"))
    (block 
      (script-comment "`instantiate-theorem' at (0 1)")
      (contrapose 
       "with(s:filtered%states,f:[states,prop],not(f(s)));")
      simplify)

    )))

(def-theorem empty_state-is-a-filtered-state
  "#(empty%state,filtered%states)"
  (theory single-filter-theory)
  (proof
   (

    (apply-macete-with-minor-premises 
     filtered%states-defining-axiom_single-filter-theory)
    (unfold-single-defined-constant-globally empty%state)

    )))

(def-theorem filtered_states-are-closed-under-takefirst
  "forall(s:filtered%states, n:nn,
     #(s(n)) implies #(takefirst{s,n},filtered%states))"
  (theory single-filter-theory)
  (proof
   (

    direct-inference
    direct-inference
    (instantiate-theorem 
     filtered%states-defining-axiom_single-filter-theory 
     ("s"))
    (block 
      (script-comment "`instantiate-theorem' at (0 0)")
      (instantiate-theorem 
       filtered%states-in-quasi-sort-domain_single-filter-theory
       ("s"))
      (beta-reduce-antecedent 
       "with(s:filtered%states,
          lambda(s:states,
            forall(n:nn,
              #(s(n))
               implies 
              forsome(b:directions,filter(s(n),b,takefirst{s,n}))))(s));")
      (instantiate-theorem 
       filtered%states-defining-axiom_single-filter-theory
       ("takefirst{s,n}"))
      (contrapose "not(with(f:[states,prop],f)(with(f:[nn,datagrams],f)));")
      (instantiate-theorem 
       states-defining-axiom_datagrams 
       ("takefirst{s,n}"))
      simplify-insistently
      (block 
	(script-comment "`instantiate-theorem' at (0 1)")
	(contrapose "not(with(f:[[nn,datagrams],prop],f)
                         (with(f:[nn,datagrams],f)));")
	simplify
	(apply-macete-with-minor-premises tr%takefirst-is-fseq)
	(apply-macete-with-minor-premises states-in-quasi-sort_datagrams)))
    (contrapose "with(s:filtered%states,not(#(s,filtered%states)));")

    )))

(def-constant has%profile
  "lambda(d:datagrams,a_1,a_2:addresses,p_1,p_2:ports,p:protocols,
     source%address(d) = a_1
      and
     destination%address(d) = a_2
      and
     source%port(d) = p_1
      and
     destination%port(d) = p_2
      and
     protocol(d) = p)"
  (theory single-filter-theory))

(def-constant initiates%tcp%connection
  "lambda(d:datagrams, 
    protocol(d) = tcp
     and
    ack in tcp%flag%set(d))"
  (theory single-filter-theory))

(def-constant tcp%connection
  "lambda(s_1:states,s_2:filtered%states,f:[nn -> nn],
          a_1,a_2:addresses,p_1,p_2:ports,
     not(s_1 = empty%state)
      and
     state%embedding(f,s_1,s_2)
      and
     has%profile(s_1(0),a_1,a_2,p_1,p_2,tcp)
      and
     forall(d:datagrams,
       in_seq{d,s_1}
        implies
       (has%profile(d,a_1,a_2,p_1,p_2,tcp)
         or
        has%profile(d,a_2,a_1,p_2,p_1,tcp)))
      and
     forall(d:datagrams,
       in_seq{d,s_1}
        implies
       if(d = s_1(0), 
          initiates%tcp%connection(d),
          not(initiates%tcp%connection(d))))
      and
     forall(m,n:nn,
       f(m) < n and n < f(m+1) 
        implies
       (not(has%profile(s_2(n),a_1,a_2,p_1,p_2,tcp))
         and
        not(has%profile(s_2(n),a_2,a_1,p_2,p_1,tcp)))))"
  (theory single-filter-theory))

(def-theorem first-datagram-in-tcp_connection-lemma
  "forall(s_1:states,s_2:filtered%states,f:[nn -> nn],
          a_1,a_2:addresses,p_1,p_2:ports,
     tcp%connection(s_1,s_2,f,a_1,a_2,p_1,p_2)
      implies
     initiates%tcp%connection(s_1(0))
      and
     has%profile(s_1(0),a_1,a_2,p_1,p_2,tcp))"
  (theory single-filter-theory)
  (proof
   (

    (unfold-single-defined-constant-globally tcp%connection)
    direct-and-antecedent-inference-strategy
    (instantiate-universal-antecedent 
     "with(p:prop,s_1:states,
        forall(d:datagrams,in_seq{d,s_1} implies if(p, p, p)));"
     ("s_1(0)"))
    (block 
      (script-comment "`instantiate-universal-antecedent' at (0 0 0)")
      (contrapose "with(p:prop,forall(i_$1:nn,p));")
      (instantiate-existential ("0")))
    (block 
      (script-comment "`instantiate-universal-antecedent' at (0 0 1)")
      (incorporate-antecedent "with(p:prop,if(p, p, p));")
      simplify)

    )))

(def-theorem tcp_connection-embedding-lemma
  "forall(s_1:states,s_2:filtered%states,f:[nn -> nn],
          a_1,a_2:addresses,p_1,p_2:ports,n:nn,
     tcp%connection(s_1,s_2,f,a_1,a_2,p_1,p_2)
      and
     #(s_1(n)) 
      implies
     s_1(n) = s_2(f(n)))"
  (theory single-filter-theory)
  (proof
   (

    (unfold-single-defined-constant-globally tcp%connection)
    (unfold-single-defined-constant-globally state%embedding)
    direct-and-antecedent-inference-strategy
    (backchain "with(p:prop,forall(n_$0:nn,p));")

    )))

