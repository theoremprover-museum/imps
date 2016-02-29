(include-files
  (files (imps theories/reals/octets)
	 (imps theories/generic-theories/indicator-supplements)
	 ))

(def-cartesian-product addresses
  (octet octet octet octet)
  (constructor make%address)
  (accessors octet_1 octet_2 octet_3 octet_4)
  (theory octets))

(def-constant address%and
  "lambda(x,y:addresses,
     make%address(logand(octet_1(x),octet_1(y)),
                  logand(octet_2(x),octet_2(y)),
                  logand(octet_3(x),octet_3(y)),
                  logand(octet_4(x),octet_4(y))))"
  (usages rewrite)
  (theory octets))

(def-constant address%xor
  "lambda(x,y:addresses,
     make%address(logxor(octet_1(x),octet_1(y)),
                  logxor(octet_2(x),octet_2(y)),
                  logxor(octet_3(x),octet_3(y)),
                  logxor(octet_4(x),octet_4(y))))"
  (usages rewrite)
  (theory octets))

(def-theorem address%and-is-total
  "total_q{address%and,[addresses,addresses -> addresses]}"
  (usages d-r-convergence)
  (theory octets)
  (proof
   (

    insistent-direct-inference
    simplify

    )))
 
(def-theorem address%xor-is-total
  "total_q{address%xor,[addresses,addresses -> addresses]}"
  (usages d-r-convergence)
  (theory octets)
  (proof
   (

    insistent-direct-inference
    simplify

    )))
 
(def-theorem equal-addresses-lemma
  "forall(a_1,a_2:addresses,
     a_1 = a_2 
      iff
     (logxor(octet_1(a_1),octet_1(a_2)) = 0#8
       and
      logxor(octet_2(a_1),octet_2(a_2)) = 0#8
       and
      logxor(octet_3(a_1),octet_3(a_2)) = 0#8
       and
      logxor(octet_4(a_1),octet_4(a_2)) = 0#8))"
  (theory octets)
  (proof
   (

    direct-inference
    direct-inference
    simplify
    (block 
      (script-comment "`direct-inference' at (1)")
      (cut-with-single-formula 
       "a_1 = make%address(octet_1(a_1),
                           octet_2(a_1),
                           octet_3(a_1),
                           octet_4(a_1))
         and
        a_2 = make%address(octet_1(a_2),
                           octet_2(a_2),
                           octet_3(a_2),
                           octet_4(a_2))")
      (block 
	(script-comment "`cut-with-single-formula' at (0)")
	(antecedent-inference "with(p:prop,p and p);")
	(backchain 
	 "with(a_2:addresses,
            a_2 = make%address(octet_1(a_2),
                               octet_2(a_2),
                               octet_3(a_2),
                               octet_4(a_2)));")
	(backchain 
	 "with(a_1:addresses,
            a_1 = make%address(octet_1(a_1),
                               octet_2(a_1),
                               octet_3(a_1),
                               octet_4(a_1)));")
	(weaken (1 0))
	simplify)
      simplify)

    )))

(def-compound-macete simplify-address-expression
  (series
   octet_1%make-addresses
   octet_2%make-addresses
   octet_3%make-addresses
   octet_4%make-addresses
   simplify))

(def-constant address%lt
  "lambda(a_1,a_2:addresses,
     octet%lt(octet_1(a_1), octet_1(a_2))
      or
     (octet_1(a_1) = octet_1(a_2)
       and
      (octet%lt(octet_2(a_1), octet_2(a_2))
        or
       (octet_2(a_1) = octet_2(a_2)
         and
        (octet%lt(octet_3(a_1), octet_3(a_2))
          or 
         (octet_3(a_1) = octet_3(a_2)
           and
          octet%lt(octet_4(a_1), octet_4(a_2))))))))"
  (usages rewrite)
  (theory octets))

(def-constant address%le
  "lambda(a_1,a_2:addresses, address%lt(a_1,a_2) or a_1 = a_2)"
  (usages rewrite)
  (theory octets))

(def-theorem address%lt-transitivity
  "forall(a_1,a_2,a_3:addresses, 
     address%lt(a_1,a_2) and address%lt(a_2,a_3) implies address%lt(a_1,a_3))"
  (theory octets)
  (proof
   (

    (unfold-single-defined-constant-globally address%lt)
    direct-inference
    direct-inference
    (antecedent-inference-strategy (0))
    (block 
      (script-comment "`antecedent-inference-strategy' at (0 0 0)")
      direct-inference
      (contrapose "with(p:prop,not(p));")
      (apply-macete-with-minor-premises octet%lt-transitivity)
      auto-instantiate-existential)
    (block 
      (script-comment "`antecedent-inference-strategy' at (0 0 1 0 0)")
      direct-inference
      (contrapose "with(p:prop,not(p));")
      (backchain "with(o:octet,o=o);"))
    (block 
      (script-comment "`antecedent-inference-strategy' at (0 0 1 0 1 0 0)")
      direct-inference
      (contrapose "with(p:prop,not(p));")
      (backchain "with(a_2,a_1:addresses,octet_1(a_1)=octet_1(a_2));"))
    (block 
      (script-comment "`antecedent-inference-strategy' at (0 0 1 0 1 0 1 0)")
      direct-inference
      (contrapose "with(p:prop,not(p));")
      (backchain "with(a_2,a_1:addresses,octet_1(a_1)=octet_1(a_2));"))
    (block 
      (script-comment "`antecedent-inference-strategy' at (0 1 0 0 0)")
      direct-inference
      (contrapose "with(p:prop,not(p));")
      (backchain-backwards "with(o:octet,o=o);"))
    (block 
      (script-comment "`antecedent-inference-strategy' at (0 1 0 0 1 0 0)")
      direct-inference
      direct-inference
      direct-inference
      (contrapose 
       "with(a_3,a_1:addresses,
          not(octet%lt(octet_2(a_1),octet_2(a_3))));")
      (apply-macete-with-minor-premises octet%lt-transitivity)
      auto-instantiate-existential)
    (block 
      (script-comment 
       "`antecedent-inference-strategy' at (0 1 0 0 1 0 1 0 0)")
      direct-inference
      direct-inference
      direct-inference
      (contrapose 
       "with(a_3,a_1:addresses,
          not(octet%lt(octet_2(a_1),octet_2(a_3))));")
      (backchain "with(a_2,a_1:addresses,octet_2(a_1)=octet_2(a_2));"))
    (block 
      (script-comment 
       "`antecedent-inference-strategy' at (0 1 0 0 1 0 1 0 1 0)")
      direct-inference
      direct-inference
      direct-inference
      (contrapose 
       "with(a_3,a_1:addresses,
          not(octet%lt(octet_2(a_1),octet_2(a_3))));")
      (backchain "with(a_2,a_1:addresses,octet_2(a_1)=octet_2(a_2));"))
    (block 
      (script-comment "`antecedent-inference-strategy' at (0 1 0 1 0 0 0)")
      direct-inference
      (contrapose "with(p:prop,not(p));")
      (backchain-backwards 
       "with(a_3,a_2:addresses,octet_1(a_2)=octet_1(a_3));"))
    (block 
      (script-comment 
       "`antecedent-inference-strategy' at (0 1 0 1 0 0 1 0 0)")
      direct-inference
      direct-inference
      direct-inference
      (contrapose 
       "with(a_3,a_1:addresses, 
          not(octet%lt(octet_2(a_1),octet_2(a_3))));")
      (backchain-backwards 
       "with(a_3,a_2:addresses,octet_2(a_2)=octet_2(a_3));"))
    (block 
      (script-comment 
       "`antecedent-inference-strategy' at (0 1 0 1 0 0 1 0 1 0 0)")
      direct-inference
      direct-inference
      direct-inference
      direct-inference
      direct-inference
      (contrapose 
       "with(a_3,a_1:addresses,
          not(octet%lt(octet_3(a_1),octet_3(a_3))));")
      (apply-macete-with-minor-premises octet%lt-transitivity)
      auto-instantiate-existential)
    (block 
      (script-comment 
       "`antecedent-inference-strategy' at (0 1 0 1 0 0 1 0 1 0 1 0)")
      direct-inference
      direct-inference
      direct-inference
      direct-inference
      direct-inference
      (contrapose 
       "with(a_3,a_1:addresses,
          not(octet%lt(octet_3(a_1),octet_3(a_3))));")
      (backchain "with(a_2,a_1:addresses,octet_3(a_1)=octet_3(a_2));"))
    (block 
      (script-comment 
       "`antecedent-inference-strategy' at (0 1 0 1 0 1 0 0)")
      direct-inference
      (contrapose "with(p:prop,not(p));")
      (backchain-backwards 
       "with(a_3,a_2:addresses,octet_1(a_2)=octet_1(a_3));"))
    (block 
      (script-comment 
       "`antecedent-inference-strategy' at (0 1 0 1 0 1 0 1 0 0)")
      direct-inference
      direct-inference
      direct-inference
      (contrapose 
       "with(a_3,a_1:addresses,
          not(octet%lt(octet_2(a_1),octet_2(a_3))));")
      (backchain-backwards 
       "with(a_3,a_2:addresses,octet_2(a_2)=octet_2(a_3));"))
    (block 
      (script-comment 
       "`antecedent-inference-strategy' at (0 1 0 1 0 1 0 1 0 1 0 0)")
      direct-inference
      direct-inference
      direct-inference
      direct-inference
      direct-inference
      (contrapose 
       "with(a_3,a_1:addresses,
          not(octet%lt(octet_3(a_1),octet_3(a_3))));")
      (backchain-backwards 
       "with(a_3,a_2:addresses,octet_3(a_2)=octet_3(a_3));"))
    (block 
      (script-comment 
       "`antecedent-inference-strategy' at (0 1 0 1 0 1 0 1 0 1 0 1 0)")
      direct-inference
      direct-inference
      direct-inference
      direct-inference
      direct-inference
      direct-inference
      (apply-macete-with-minor-premises octet%lt-transitivity)
      auto-instantiate-existential)

    )))

