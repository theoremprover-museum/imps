(load-section networks)

(def-cartesian-product service
  (protocols ports)
  (theory filtered-networks)
  (constructor make%service)
  (accessors service%protocol server%port))

(def-bnf global-policy
  (theory filtered-networks)
  (base-type service%direction)
  (atoms (to_server service%direction)
	 (from_server service%direction)))

(def-atomic-sort iface%seq
  "lambda(is:[nn->ifaces], f_seq_q{is})"
  (theory filtered-networks)
  (witness "nil{ifaces}"))

(def-constant uses%service
  "lambda(dg:datagrams, s:service, dir:service%direction, 
      service%protocol(s)=protocol(dg) and
      if(dir=to_server, destination%port, source%port)(dg) 
	=server%port(s))"
  (theory global-policy))


(def-constant from%region
  "lambda(is:iface%seq, f,t:sets[ifaces],
     forsome(j,k:nn, j<k and is(j) in f and is(k) in t))"
  (theory global-policy))

(def-cartesian-product pre%traject
   (datagrams netstates iface%seq)
   (theory global-policy)
   (constructor make%trajectory)
   (accessors traject%dg traject%ns traject%is))

(def-theorem trajectories-exist
  "forsome(x:pre%traject,
  traject%is(x)
  =trajectory(traject%dg(x),traject%ns(x),traject%is(x)(0)))"
  (theory global-policy))

(def-atomic-sort traject
  "lambda(pt:pre%traject,
     traject%is(pt)
      =trajectory(traject%dg(pt), traject%ns(pt), traject%is(pt)(0)))"
  (theory global-policy))



