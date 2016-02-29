(include-files
  (files (imps theories/networks/network-states)
	 (imps theories/networks/trajectory)
	 ))

(def-language filtered-network-language
  (embedded-languages routed-networks)
  (base-types directions actions)
  (sorts
   (filters "[datagrams,directions,states -> actions]")
   )
  (constants
   (inbound directions)
   (outbound directions)
   (accept actions)
   (reject actions)
   (drop actions)
   (netstate "[netstates, zz -> prop]")
   (iface%filter "[ifaces -> filters]")
   (at%router "[datagrams, hosts, zz -> prop]")
   (delivered "[datagrams, hosts, zz -> prop]")
   (failed%delivery "[datagrams, hosts, zz -> prop]")
   (inbound%at%iface "[datagrams, ifaces, zz -> prop]")
   (outbound%at%iface "[datagrams, ifaces, addresses, zz -> prop]")
   (filtered%out "[datagrams, ifaces, directions, actions, zz -> prop]")
   ))

(def-theory filtered-networks
  (language filtered-network-language)
  (component-theories routed-networks)
  (distinct-constants 
   (inbound outbound)
   (accept reject drop))
  (axioms

   (iface_router-is-total
    "total_q{iface%filter, [ifaces -> filters]}")

   (delivery-transition
    "forall(d:datagrams, h:hosts, i:ifaces, k:zz,
       destination%address(d) in addresses%of%host(h)
        implies
       at%router(d,h,k)
        iff
       delivered(d,h,k))")

   (forwarding-transition
    "forall(d:datagrams, h:hosts, i:ifaces, a:addresses, k:zz,
       routing%fn(host%router(h),d) = make%route%component(i,a)
        implies
       at%router(d,h,k)
        iff
       outbound%at%iface(d,i,a,k))")

   (failed-delivery-transition
    "forall(d:datagrams, h:hosts, k:zz,
       not(#(routing%fn(host%router(h),d)))
        implies
       at%router(d,h,k)
        iff
       failed%delivery(d,h,k))")

   (inbound-filtering-transition
    "forall(d:datagrams, h:hosts, i:ifaces, act:actions, n:netstates, 
            k:zz,
       h = iface%host(i)
        and 
       netstate(n,k)
        and
       i in ifaces%of%host(h)
        and 
       iface%filter(i)(d,inbound,n(h)) = act
        implies
       inbound%at%iface(d,i,k) 
        iff
       if_form(act = accept, 
               at%router(d,h,k), 
               filtered%out(d,i,inbound,act,k)))")

   (outbound-filtering-transition
    "forall(d:datagrams, h:hosts, i:ifaces, a:addresses, act:actions, 
            n:netstates, k:zz, 
       h = iface%host(i)
        and
       netstate(n,k)
        and
       i in ifaces%of%host(h)
        and 
       iface%filter(i)(d,outbound,n(h)) = act
        and
       routing%fn(host%router(h),d) = make%route%component(i,a)
        and
       #(addr%to%iface(a))
        implies
       outbound%at%iface(d,i,a,k)
        iff
       if_form(act = accept, 
               inbound%at%iface(d,addr%to%iface(a),k+1), 
               filtered%out(d,i,outbound,act,k)))")

   (state-transition
    "forall(d:datagrams, h:hosts, n:netstates, k:zz,
       at%router(d,h,k)
        implies
       netstate(n,k)
        iff
       netstate(append%to%netstate(n,h,d),k+1))")
   
   ))

(def-constant iface%out%to%in
  "lambda(out%i:ifaces,d:datagrams,n:netstates,
     iota(in%i:ifaces,
       iface%filter(out%i)(d,outbound,n(iface%host(out%i))) = accept
        and
       in%i = next%hop%iface(routing%fn(host%router(iface%host(out%i)),d))))"
  (theory filtered-networks))

(def-constant iface%in%to%out
  "lambda(in%i:ifaces,d:datagrams,n:netstates,
     iota(out%i:ifaces,
       iface%filter(in%i)(d,inbound,n(iface%host(out%i))) = accept
        and
       out%i = out%iface(routing%fn(host%router(iface%host(in%i)),d))))"
  (theory filtered-networks))

(def-theorem iface_out_to_in-macete
  "forall(i:ifaces, d:datagrams, a:addresses, n:netstates, k:zz,
     netstate(n,k) 
      and 
     routing%fn(host%router(iface%host(i)),d) = make%route%component(i,a)
      and
     #(iface%out%to%in(i,d,n))
      implies
     outbound%at%iface(d,i,a,k)
      iff
     inbound%at%iface(d,iface%out%to%in(i,d,n),k+1))"
  (theory filtered-networks)
  (proof
   (

    (unfold-single-defined-constant-globally iface%out%to%in)
    (eliminate-defined-iota-expression 0 w)
    direct-inference
    (instantiate-theorem 
     outbound-filtering-transition
     ("d" "iface%host(i)" "i" "a" "accept" "n" "k"))
    (block 
      (script-comment "`instantiate-theorem' at (0 0 2)")
      (contrapose "with(p:prop,not(p));")
      (apply-macete-with-minor-premises iface-is-an-iface-of-host))
    (block 
      (script-comment "`instantiate-theorem' at (0 0 5)")
      (contrapose "with(p:prop,not(p));")
      (instantiate-theorem 
       next_hop_iface-lemma 
       ("iface%host(i)" "d" "i" "a")))
    (move-to-ancestor 2)
    (block 
      (script-comment "`instantiate-theorem' at (0 1)")
      (instantiate-theorem 
       next_hop_iface-lemma 
       ("iface%host(i)" "d" "i" "a"))
      simplify)

    )))

(def-theorem iface_in_to_out-macete
  "forall(i:ifaces, d:datagrams, a:addresses, n:netstates, k:zz,
     netstate(n,k) 
      and 
     (routing%fn(host%router(iface%host(i)),d) 
       = 
      make%route%component(iface%in%to%out(i,d,n),a))
      implies
     inbound%at%iface(d,i,k)
      iff
     outbound%at%iface(d,iface%in%to%out(i,d,n),a,k))"
  (theory filtered-networks)
  (proof
   (

    (unfold-single-defined-constant-globally iface%in%to%out)
    (eliminate-defined-iota-expression 0 u)
    direct-inference
    (cut-with-single-formula "iface%host(i)=iface%host(u)")
    (move-to-sibling 1)
    (block 
      (script-comment "`cut-with-single-formula' at (1)")
      (backchain "with(p:prop,p and p);")
      (apply-macete-with-minor-premises host-of-out_iface))
    (block 
      (script-comment "`cut-with-single-formula' at (0)")
      (instantiate-theorem 
       inbound-filtering-transition
			   
       ("d" "iface%host(i)" "i" "accept" "n" "k"))
      (block 
	(script-comment "`instantiate-theorem' at (0 0 2)")
	(contrapose "with(p:prop,not(p));")
	(apply-macete-with-minor-premises iface-is-an-iface-of-host))
      (block 
	(script-comment "`instantiate-theorem' at (0 0 3)")
	(contrapose "with(p:prop,not(p));")
	simplify)
      (block 
	(script-comment "`instantiate-theorem' at (0 1 0 0)")
	simplify
	(instantiate-theorem 
	 forwarding-transition
			     
	 ("d" "iface%host(i)" "u" "a" "k")))
      (block 
	(script-comment "`instantiate-theorem' at (0 1 1 0)")
	(instantiate-theorem 
	 forwarding-transition
			     
	 ("d" "iface%host(i)" "u" "a" "k"))
	simplify))

    )))

(def-translation packet-trajectory-theory-to-filtered-networks
  (source packet-trajectory-theory)
  (target filtered-networks)
  (fixed-theories h-o-real-arithmetic)
  (sort-pairs
   (ifaces ifaces)
   (datagrams datagrams)
   (netstates netstates))
  (constant-pairs
   (iface%out%to%in iface%out%to%in)
   (iface%in%to%out iface%in%to%out))
  dont-enrich)

(def-transported-symbols trajectory
  (translation packet-trajectory-theory-to-filtered-networks))
