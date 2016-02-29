(include-files
  (files (imps theories/networks/datagrams)))
	 
(def-constant empty%state
  "nil{datagrams}"
  (theory datagrams))

(def-theorem states-exist
  "forsome(x:[nn,datagrams],f_seq_q{x})"
  (theory datagrams)
  (proof 
   (
    
    (instantiate-existential ("empty%state"))
    (unfold-single-defined-constant-globally empty%state)
    (apply-macete-with-minor-premises tr%nil-is-fseq)

    )))

(def-atomic-sort states 
  "lambda(s:[nn -> datagrams], f_seq_q{s})"
  (theory datagrams))

(def-theorem empty_state-is-a-state
  "#(empty%state,states)"
  (theory datagrams)
  (proof
   (

    (apply-macete-with-minor-premises states-defining-axiom_datagrams)
    (unfold-single-defined-constant-globally empty%state)
    (apply-macete-with-minor-premises tr%nil-is-fseq)

    )))

(def-constant append%to%state
  "lambda(s:states, d:datagrams,
     append(s,cons(d,empty%state)))"
  (theory datagrams))

(def-theorem append_to_state-is-total
  "total_q{append%to%state,[states,datagrams -> [nn -> datagrams]]}"
  (usages d-r-convergence)
  (theory datagrams)
  (proof
   (

    insistent-direct-inference
    (unfold-single-defined-constant-globally append%to%state)

    )))

(def-theorem append_to_state-is-defined-in-states
  "forall(s:states, d:datagrams, #(append%to%state(s,d),states))"
  (usages d-r-convergence)
  (theory datagrams)
  (proof
   (

    (apply-macete-with-minor-premises states-defining-axiom_datagrams)
    beta-reduce-repeatedly
    direct-inference
    (unfold-single-defined-constant-globally append%to%state)
    (unfold-single-defined-constant-globally empty%state)
    (apply-macete-with-minor-premises tr%append-is-fseq)
    (apply-macete-with-minor-premises tr%cons-to-nil-is-fseq)
    (instantiate-theorem states-defining-axiom_datagrams ("s_$0"))
    (simplify-antecedent "with(s_$0:states,not(#(s_$0,states)));")

    )))

(def-constant state%embedding
  "lambda(f:[nn -> nn],s_1,s_2:states,
     dom{f} = dom{s_1}
      and
     forall(m,n:nn, m < n and n < length{s_1} implies f(m) < f(n))
      and
     forall(n:nn, #(s_1(n)) implies s_1(n) = s_2(f(n))))"
  (theory datagrams))
