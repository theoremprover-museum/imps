(include-files
  (files (imps theories/networks/filters)))

(def-language one-route-network-language
  (embedded-language filtered-networks)
  (constants
   (addr_a addresses)
   (addr_b addresses)))

(def-theory one-route-networks
  (language one-route-network-language)
  (component-theories filtered-networks)
  (axioms
   (addr_a-is-an-address-of-an-interface
    "#(addr%to%iface(addr_a))")
   (addr_b-is-an-address-of-an-interface
    "#(addr%to%iface(addr_b))")
   (restriction-of-datagrams
    "forall(d:datagrams,
       (source%address(d) = addr_a and destination%address(d) = addr_b)
        or
       (source%address(d) = addr_b and destination%address(d) = addr_a))")))

(def-constant iface_a
  "addr%to%iface(addr_a)"
  (theory one-route-networks))

(def-constant iface_b
  "addr%to%iface(addr_b)"
  (theory one-route-networks))

