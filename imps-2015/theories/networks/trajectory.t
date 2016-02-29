(include-files
  (files (imps theories/networks/biiterate)))

(def-language packet-trajectory-language
  (base-types ifaces datagrams netstates)
  (constants
   (iface%out%to%in "[ifaces,datagrams,netstates -> ifaces]")
   (iface%in%to%out "[ifaces,datagrams,netstates -> ifaces]")))

(def-theory packet-trajectory-theory
  (component-theories h-o-real-arithmetic)
  (language packet-trajectory-language))

'(def-cartesian-product packet%state
  (ifaces netstates)
  (theory packet-trajectory-theory)
  (constructor make%packet%state)
  (accessors iface netstate))

(def-translation generic-theory-1-to-packet-trajectory
  (source generic-theory-1)
  (target packet-trajectory-theory)
  (fixed-theories h-o-real-arithmetic)
  (sort-pairs (ind_1 ifaces))
  (theory-interpretation-check using-simplification))

(def-renamer gt1-to-sn-renamer
  (pairs (biiterate dgrm%biiterate)
	 (iterate dgrm%iterate)))

(def-transported-symbols (biiterate iterate)
  (renamer gt1-to-sn-renamer)
  (translation generic-theory-1-to-packet-trajectory))

(def-constant trans%out%in
  "lambda(d:datagrams, x:netstates,
          lambda(i:ifaces,iface%out%to%in(i,d,x)))"
  (theory packet-trajectory-theory))

(def-constant trans%in%out
  "lambda(d:datagrams, x:netstates,
          lambda(i:ifaces,iface%in%to%out(i,d,x)))"
  (theory packet-trajectory-theory))


;; starts with iface%out%to%in

(def-constant trajectory
  "lambda(d:datagrams, x:netstates, i:ifaces,
     lambda(n:zz, dgrm%biiterate(trans%in%out(d,x),trans%out%in(d,x),i)(n)))"
  (theory packet-trajectory-theory))
