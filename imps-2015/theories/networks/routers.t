(include-files
  (files (imps theories/networks/networks)
	 (imps theories/networks/datagrams)))

(def-cartesian-product route%components
  (ifaces addresses)
  (constructor make%route%component)
  (accessors out%iface next%hop%addr)
  (theory networks))

(def-language routed-network-language
  (embedded-language networks)
  (sorts
   (routers "[sets[addresses] -> route%components]")
   )
  (constants
   (host%router "[hosts -> routers]")
   ))

(def-theory routed-networks
  (language routed-network-language)
  (component-theories networks datagrams)
  (axioms
   (host_router-is-total
    "total_q{host%router, [hosts -> routers]}"
    d-r-convergence)
   (elements-of-host_router-domain-are-disjoint
    "forall(h:hosts,s_1,s_2:sets[addresses], 
       #(host%router(h)(s_1)) and #(host%router(h)(s_2)) and not s_1 = s_2
        implies 
       s_1 disj s_2)")
   (out_iface-is-an-interface-of-host
    "forall(h:hosts, s:sets[addresses],
       #(host%router(h)(s)) 
        implies
       out%iface(host%router(h)(s)) in ifaces%of%host(h))")
   (next_hop_addr-is-an-address-of-out_iface-spnet
    "forall(h:hosts, s:sets[addresses],
       #(host%router(h)(s)) 
        implies
       next%hop%addr(host%router(h)(s))
        in
       addresses%of%spnet(iface%spnet(out%iface(host%router(h)(s)))))")
   ))

(def-constant next%hop%iface
  "lambda(c:route%components, addr%to%iface(next%hop%addr(c)))"
  (theory routed-networks))

(def-constant routing%fn
  "lambda(r:[sets[addresses] -> route%components], d:datagrams,
     iota(c:route%components, 
       forsome(addr%set:sets[addresses],
         destination%address(d) in addr%set
          and
         c = r(addr%set))))"
  (theory routed-networks))

(def-theorem host-of-out_iface
  "forall(h:hosts, d:datagrams,
     #(routing%fn(host%router(h),d))
      implies
     iface%host(out%iface(routing%fn(host%router(h),d)))=h)"
  (theory routed-networks)
  (proof
   (

    (unfold-single-defined-constant-globally routing%fn)
    direct-and-antecedent-inference-strategy
    (eliminate-defined-iota-expression 0 w)
    (antecedent-inference "with(p:prop,forsome(addr%set:sets[addresses],p));")
    (instantiate-theorem out_iface-is-an-interface-of-host ("h" "addr%set"))
    (weaken (3 2))
    (incorporate-antecedent "with(f:ifaces,f) in with(f:sets[ifaces],f);")
    (unfold-single-defined-constant-globally ifaces%of%host)
    simplify-insistently
    direct-and-antecedent-inference-strategy
    (backchain "with(f:ifaces,f)=with(f:pre%ifaces,f);")
    simplify

    )))

(def-theorem next_hop_iface-lemma
  "forall(h:hosts, d:datagrams, i:ifaces, a:addresses,
     routing%fn(host%router(h),d) = make%route%component(i,a)
      implies
     next%hop%iface(routing%fn(host%router(h),d)) == addr%to%iface(a))"
  (theory routed-networks)
  (proof
   (

    direct-and-antecedent-inference-strategy
    (unfold-single-defined-constant-globally next%hop%iface)
    (backchain "with(p:prop,p);")
    simplify

    )))