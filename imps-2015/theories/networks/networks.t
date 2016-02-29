(load-section basic-cardinality)

(include-files
  (files (imps theories/networks/address-applications)))

(def-language pre-network-language
  (base-types hosts spnets)
  (sorts (loopbacks spnets))
  (constants 
   (iface%relation "[hosts, spnets -> prop]")
   (loopback%spnet "[hosts -> loopbacks]")
   ))

(def-theory pre-networks
  (language pre-network-language)
  (component-theories h-o-real-arithmetic)
  (axioms

   (loopback_spnet-is-bijective
    "bijective_q{loopback%spnet}")

   (loopback_spnet-gives-spnet-with-a-single-host
    "forall(h:hosts, 
       indic{h_1:hosts, iface%relation(h_1,loopback%spnet(h))} 
        = 
       singleton{h})")

   ))

(def-theorem loopback_spnet-host
  "forall(h:hosts, iface%relation(h,loopback%spnet(h)))"
  (theory pre-networks)
  (proof
   (

    direct-inference
    (instantiate-theorem 
     loopback_spnet-gives-spnet-with-a-single-host 
     ("h"))
    (contrapose "with(p:prop,p);")
    extensionality
    (instantiate-existential ("h"))
    simplify

    )))

(def-theorem loopback_spnet-is-total
  "total_q{loopback%spnet,[hosts -> loopbacks]}"
  (theory pre-networks)
  (usages d-r-convergence)
  (proof
   (

    insistent-direct-inference
    (instantiate-theorem loopback_spnet-host ("x_0"))

    )))

(def-cartesian-product pre%ifaces
  (hosts spnets)
  (constructor make%pre%iface)
  (accessors iface%host iface%spnet)
  (theory pre-networks))

(def-theorem interfaces-exist
  "forsome(x:pre%ifaces,
     iface%relation(iface%host(x),iface%spnet(x)))"
  (theory pre-networks)
  (proof
   (

    (instantiate-existential 
     ("with(h:hosts,make%pre%iface(h,loopback%spnet(h)))"))
    simplify
    (apply-macete-with-minor-premises loopback_spnet-host)

    )))

(def-atomic-sort ifaces
  "lambda(p:pre%ifaces, 
     iface%relation(iface%host(p), iface%spnet(p)))"
  (theory pre-networks))

(def-constant loopback%iface
  "lambda(h:hosts, make%pre%iface(h,loopback%spnet(h)))"
  (theory pre-networks))

(def-constant hosts%of%spnet
  "lambda(s:spnets, indic{h:hosts, iface%relation(h,s)})"
  (theory pre-networks))

(def-constant is%loopback%spnet
  "lambda(s:spnets, f_card{hosts%of%spnet(s)} = 1)"
  (theory pre-networks))

(def-theorem loopback_spnet-gives-a-loopback-spnet
  "forall(h:hosts, is%loopback%spnet(loopback%spnet(h)))"
  (theory pre-networks)
  (proof
   (

    direct-inference
    (unfold-single-defined-constant-globally is%loopback%spnet)
    (apply-macete-with-minor-premises tr%singleton-has-f-card-one)
    (block 
      (script-comment "`apply-macete-with-minor-premises' at (0)")
      (instantiate-existential ("h"))
      (unfold-single-defined-constant-globally hosts%of%spnet)
      (instantiate-theorem 
       loopback_spnet-gives-spnet-with-a-single-host
       ("h")))
    simplify

    )))

(def-constant is%point%to%point%spnet
  "lambda(s:spnets, f_card{hosts%of%spnet(s)} = 2)"
  (theory pre-networks))

(def-constant spnets%of%host
  "lambda(h:hosts, indic{s:spnets, iface%relation(h,s)})"
  (theory pre-networks))

(def-constant is%single%homed
  "lambda(h:hosts, 2 = f_card{spnets%of%host(h)})"
  (theory pre-networks))

(def-constant is%multi%homed
  "lambda(h:hosts, 3 <= f_card{spnets%of%host(h)})"
  (theory pre-networks))

(def-language network-language
  (embedded-languages pre-networks octets)
  (constants 
   (address%relation "[ifaces, addresses -> prop]")
   (mask%relation "[ifaces, masks -> prop]")
   ))

(def-theory networks
  (language network-language)
  (component-theories pre-networks octets)
  (axioms

   (loopback-interface-has-loopback%address
    "forall(h:hosts, 
       address%relation(loopback%iface(h),loopback%address))")

   (loopback-interface-has-loopback%mask
    "forall(h:hosts, 
       mask%relation(loopback%iface(h),loopback%mask))")

   ))

(def-constant addr%to%iface
  "lambda(a:addresses, iota(i:ifaces, address%relation(i,a)))"
  (theory networks))

(def-constant ifaces%of%host
  "lambda(h:hosts,
     indic{i:ifaces,
       forsome(s:spnets, 
         i = make%pre%iface(h,s) and iface%relation(h,s))})"
  (theory networks))

(def-theorem iface-is-an-iface-of-host
  "forall(i:ifaces, i in ifaces%of%host(iface%host(i)))"
  (theory networks)
  (proof
   (

    direct-inference
    (unfold-single-defined-constant-globally ifaces%of%host)
    simplify-insistently
    (instantiate-existential ("iface%spnet(i)"))
    simplify
    (apply-macete-with-minor-premises 
     ifaces-in-quasi-sort_pre-networks)

    )))

(def-constant ifaces%of%spnet
  "lambda(s:spnets,
     indic{i:ifaces,
       forsome(h:hosts,
         i = make%pre%iface(h,s) and iface%relation(h,s))})"
  (theory networks))

(def-constant addresses%of%host
  "lambda(h:hosts,
     indic{a:addresses, 
       forsome(i:ifaces, 
         h = iface%host(i) and address%relation(i,a))})"
  (theory networks))

(def-constant masks%of%host
  "lambda(h:hosts,
     indic{m:masks, 
       forsome(i:ifaces, 
         h = iface%host(i) and mask%relation(i,m))})"
  (theory networks))

(def-constant addresses%of%spnet
  "lambda(s:spnets,
     indic{a:addresses, 
       forsome(i:ifaces, 
         s = iface%spnet(i) and address%relation(i,a))})"
  (theory networks))

(def-constant masks%of%spnet
  "lambda(s:spnets,
     indic{m:masks,
       forsome(i:ifaces, 
         s = iface%spnet(i) and mask%relation(i,m))})"
  (theory networks))

(def-constant spnet%is%conventional
  "lambda(s:spnets, 
     forsome(m:masks,
       forall(i:ifaces, 
         iface%spnet(i) = s implies mask%relation(i,m))))"
  (theory networks))

(def-constant network%is%conventional
  "forall(s:spnets, spnet%is%conventional(s))"
  (theory networks))

(def-constant spnet%mask
  "lambda(s:spnets, 
     iota(m:masks, 
       forall(i:ifaces, 
         iface%spnet(i) = s implies mask%relation(i,m))))"
  (theory networks))

(def-constant spnet%address
  "lambda(s:spnets,
     iota(a:addresses,
       forall(i:ifaces, b:addresses,
         iface%spnet(i) = s
          and
         address%relation(i,b) 
          implies
         a = address%and(b,spnet%mask(s)))))"
  (theory networks))

(def-constant directly%connected
  "lambda(h_1,h_2:hosts, 
     forsome(s:spnets, 
       h_1 in hosts%of%spnet(s) and h_2 in hosts%of%spnet(s)))"
  (theory networks))

(def-recursive-constant connected
  "lambda(con:[hosts,hosts -> prop],
     lambda(h_1,h_2:hosts, 
       directly%connected(h_1,h_2) 
        or
       forsome(h_3:hosts, directly%connected(h_1,h_3) and con(h_3,h_2))))"
  (theory networks))

(def-theorem host-spnet-inversion
  "forall(h:hosts, s:spnets, 
     h in hosts%of%spnet(s) iff s in spnets%of%host(h))"
  (theory networks)
  (proof
   (

    direct-inference
    unfold-defined-constants
    simplify-insistently

    )))

(def-theorem hosts-are-self-connected
  "forall(h:hosts, connected(h,h))"
  (theory networks)
  (proof
   (

    direct-inference
    (unfold-single-defined-constant-globally connected)
    direct-and-antecedent-inference-strategy
    (contrapose "with(p:prop,p);")
    (unfold-single-defined-constant-globally directly%connected)
    (instantiate-existential ("loopback%spnet(h)"))
    (unfold-single-defined-constant-globally hosts%of%spnet)
    simplify-insistently
    (apply-macete-with-minor-premises loopback_spnet-host)

    )))