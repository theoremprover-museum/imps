(include-files
  (files (imps theories/networks/states)
	 (imps theories/networks/routers)))

(def-theorem netstates-exist
  "forsome(x:[hosts,states],total_q{x,[hosts,states]})"
  (theory routed-networks)
  (proof 
   (

    (instantiate-existential ("lambda(h:hosts, nil{datagrams})"))
    (block 
      (script-comment "`instantiate-existential' at (0)")
      insistent-direct-inference
      beta-reduce-repeatedly)
    (block 
      (script-comment "`instantiate-existential' at (1)")
      sort-definedness
      simplify)

    )))

(def-atomic-sort netstates
  "lambda(n:[hosts -> states], total_q{n,[hosts -> states]})"
  (theory routed-networks))

(def-constant append%to%netstate
  "lambda(n:netstates, h:hosts, d:datagrams, 
     lambda(h_1:hosts, if(h_1 = h, append%to%state(n(h_1),d), n(h_1))))"
  (theory routed-networks))

(def-theorem append_to_netstate-is-total
  "total_q{append%to%netstate, 
           [netstates, hosts, datagrams -> [hosts -> [nn -> datagrams]]]}"
  (usages d-r-convergence)
  (theory routed-networks)
  (proof
   (

    insistent-direct-inference
    (unfold-single-defined-constant-globally append%to%netstate)

    )))

(def-theorem append_to_netstate-is-defined-in-netstates
  "forall(n:netstates, h:hosts, d:datagrams,
     #(append%to%netstate(n,h,d),netstates))"
  (usages d-r-convergence)
  (theory routed-networks)
  (proof
   (

    direct-inference
    (apply-macete-with-minor-premises 
     netstates-defining-axiom_routed-networks)
    (cut-with-single-formula 
     "#(append%to%netstate(n,h,d),[hosts,states])")
    (block 
      (script-comment "`cut-with-single-formula' at (0)")
      beta-reduce-repeatedly
      insistent-direct-inference
      (unfold-single-defined-constant-globally append%to%netstate)
      (raise-conditional (0))
      simplify
      (instantiate-theorem 
       netstates-defining-axiom_routed-networks ("n")))
    (block 
      (script-comment "`cut-with-single-formula' at (1)")
      (unfold-single-defined-constant-globally append%to%netstate)
      sort-definedness
      direct-inference
      (case-split ("xx_0=h"))
      (block 
	(script-comment "`case-split' at (1)")
	simplify
	(apply-macete-with-minor-premises 
	 append_to_state-is-defined-in-states))
      simplify)

    )))

