(include-files
  (files (imps theories/networks/addresses)))

(def-constant masked%on
  "lambda(x, mask:octet,  logand(x,mask)=mask)"
  (theory octets))

(def-constant masked%off
  "lambda(x, mask:octet,  logand(x,mask)=0#8)"
  (theory octets))

(def-constant class%a
  "lambda(x:addresses, masked%off(octet_1(x), 128#8))"
  (theory octets))

(def-constant class%b
  "lambda(x:addresses,  masked%on(octet_1(x), 128#8) and  
                        masked%off(octet_1(x), 64#8))"
  (theory octets))

(def-constant class%c
  "lambda(x:addresses,  masked%on(octet_1(x), 128#8) and  
                        masked%on(octet_1(x), 64#8) and
                        masked%off(octet_1(x), 32#8))"
  (theory octets))

(def-constant class%d
  "lambda(x:addresses,  masked%on(octet_1(x), 128#8) and  
                        masked%on(octet_1(x), 64#8) and
                        masked%on(octet_1(x), 32#8) and
                        masked%off(octet_1(x),16#8))"
  (theory octets))

(def-constant class%e
  "lambda(x:addresses,  masked%on(octet_1(x), 128#8) and  
                        masked%on(octet_1(x), 64#8) and
                        masked%on(octet_1(x), 32#8) and
                        masked%on(octet_1(x), 16#8) and
                        masked%off(octet_1(x), 8#8))"
  (theory octets))

(def-constant net%id
  "lambda(x:addresses, 
     if(class%a(x), make%address(octet_1(x),0#8,0#8,0#8),
        class%b(x), make%address(octet_1(x),octet_2(x),0#8,0#8),
        class%c(x), make%address(octet_1(x),octet_2(x),octet_3(x),0#8),
        ?addresses))"
  (theory octets))

(def-atomic-sort masks
  "lambda(x:addresses, truth)"
  (theory octets))

(def-constant class%a%mask
  "make%address(255#8,0#8,0#8,0#8)"
  (sort "masks")
  (theory octets))

(def-constant class%b%mask
  "make%address(255#8,255#8,0#8,0#8)"
  (sort "masks")
  (theory octets))

(def-constant class%c%mask
  "make%address(255#8,255#8,255#8,0#8)"
  (sort "masks")
  (theory octets))

(def-constant loopback%address
  "make%address(127#8,0#8,0#8,1#8)"
  (theory octets))

(def-constant loopback%mask
  "class%a%mask"
  (theory octets))

(def-constant subnet
  "lambda(a:addresses,m:masks,
     indic{a_1:addresses, 
      address%and(a,m) = address%and(a_1,m)})"
  (theory octets))

(def-theorem subnet-is-total
  "total_q{subnet,[addresses,masks -> sets[addresses]]}"
  (usages d-r-convergence)
  (theory octets)
  (proof
   (

    insistent-direct-inference
    (unfold-single-defined-constant-globally subnet)
    
    )))

(def-theorem subnet-disjointness
  "forall(a_1,a_2:addresses, m_1,m_2:masks,
     subnet(a_1,m_1) disj subnet(a_2,m_2)
       iff
     not(address%and(a_1,address%and(m_1,m_2))
          =
         address%and(a_2,address%and(m_1,m_2))))"
  (theory octets)
  (proof
   (

    direct-inference
    direct-inference
    (block 
      (script-comment "`direct-inference' at (0)")
      (contrapose "with(p:prop,p);")
      (instantiate-existential 
       ("address%xor(address%and(a_1,address%and(m_1,m_2)),
                     address%xor(address%and(address%xor(m_1,m_2),
                                             address%and(a_1,m_1)),
                                 address%and(address%xor(m_1,m_2),
                                             address%and(a_2,m_2))))"))
      (move-to-ancestor 1)
      (incorporate-antecedent "with(p:prop,p);")
      (unfold-single-defined-constant-globally subnet)
      simplify-insistently
      (apply-macete-with-minor-premises simplify-address-expression)
      (apply-macete-with-minor-premises logand-simplification-lemma-1)
      (apply-macete-with-minor-premises logand-is-idempotent)
      simplify)
    (block 
      (script-comment "`direct-inference' at (1)")
      (contrapose "with(p:prop,p);")
      (antecedent-inference "with(p:prop,p);")
      (incorporate-antecedent "with(p:prop,p);")
      (unfold-single-defined-constant-globally subnet)
      simplify-insistently
      direct-and-antecedent-inference-strategy
      (block 
	(script-comment 
	 "`direct-and-antecedent-inference-strategy' at (0 0 0 0 0)")
	(force-substitution 
	 "logand(octet_1(m_2),octet_1(m_1))"
	 "logand(octet_1(m_1),octet_1(m_2))"
	 (1))
	(apply-macete-with-minor-premises associativity-of-logand)
	(force-substitution 
	 "logand(octet_1(m_1),octet_1(a_1))"
	 "logand(octet_1(m_1),octet_1(x))"
	 (0))
	(block 
	  (script-comment "`force-substitution' at (0)")
	  (force-substitution 
	   "logand(octet_1(m_2),octet_1(a_2))"
	   "logand(octet_1(m_2),octet_1(x))"
	   (0))
	  simplify
	  simplify)
	simplify)
      (block 
	(script-comment 
	 "`direct-and-antecedent-inference-strategy' at (0 1 0 0 0)")
	(force-substitution 
	 "logand(octet_2(m_2),octet_2(m_1))"
	 "logand(octet_2(m_1),octet_2(m_2))"
	 (1))
	(apply-macete-with-minor-premises associativity-of-logand)
	(force-substitution 
	 "logand(octet_2(m_1),octet_2(a_1))"
	 "logand(octet_2(m_1),octet_2(x))"
	 (0))
	(block 
	  (script-comment "`force-substitution' at (0)")
	  (force-substitution 
	   "logand(octet_2(m_2),octet_2(a_2))"
	   "logand(octet_2(m_2),octet_2(x))"
	   (0))
	  simplify
	  simplify)
	simplify)
      (block 
	(script-comment 
	 "`direct-and-antecedent-inference-strategy' at (0 2 0 0 0)")
	(force-substitution 
	 "logand(octet_3(m_2),octet_3(m_1))"
	 "logand(octet_3(m_1),octet_3(m_2))"
	 (1))
	(apply-macete-with-minor-premises associativity-of-logand)
	(force-substitution 
	 "logand(octet_3(m_1),octet_3(a_1))"
	 "logand(octet_3(m_1),octet_3(x))"
	 (0))
	(block 
	  (script-comment "`force-substitution' at (0)")
	  (force-substitution 
	   "logand(octet_3(m_2),octet_3(a_2))"
	   "logand(octet_3(m_2),octet_3(x))"
	   (0))
	  simplify
	  simplify)
	simplify)
      (block 
	(script-comment 
	 "`direct-and-antecedent-inference-strategy' at (0 3 0 0 0)")
	(force-substitution 
	 "logand(octet_4(m_2),octet_4(m_1))"
	 "logand(octet_4(m_1),octet_4(m_2))"
	 (1))
	(apply-macete-with-minor-premises associativity-of-logand)
	(force-substitution 
	 "logand(octet_4(m_1),octet_4(a_1))"
	 "logand(octet_4(m_1),octet_4(x))"
	 (0))
	(block 
	  (script-comment "`force-substitution' at (0)")
	  (force-substitution 
	   "logand(octet_4(m_2),octet_4(a_2))"
	   "logand(octet_4(m_2),octet_4(x))"
	   (0))
	  simplify
	  simplify)
	simplify))

    )))

(def-compound-macete simplify-subnet-disjointness-assertion
  (series
   subnet-disjointness
   simplify
   simplify-address-expression))
   
(def-compound-macete simplify-address-set-disjointness-assertion
  (series
   (repeat
    tr%union-disjointness-left
    tr%union-disjointness-right)
   simplify-subnet-disjointness-assertion))
   
(def-constant rangenet
  "lambda(a_1,a_2:addresses,
     indic{a:addresses, address%le(a_1,a) and address%le(a,a_2)})"
  (theory octets))

(def-theorem rangenet-is-total
  "total_q{rangenet,[addresses,addresses -> sets[addresses]]}"
  (usages d-r-convergence)
  (theory octets)
  (proof
   (

    insistent-direct-inference
    (unfold-single-defined-constant-globally rangenet)
    
    )))

(def-theorem rangenet-disjointness
  "forall(a_1,a_2,b_1,b_2:addresses,
     rangenet(a_1,a_2) disj rangenet(b_1,b_2)
       iff
     (address%lt(a_2,a_1)
       or
      address%lt(b_2,b_1)
       or
      address%lt(a_2,b_1) 
       or 
      address%lt(b_2,a_1)))"
  (theory octets)
  (proof
   (

)))

