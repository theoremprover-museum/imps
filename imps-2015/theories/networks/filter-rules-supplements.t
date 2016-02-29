(include-files
  (files (imps theories/networks/filter-rules)))

(def-script subnet-simplification 1
  (
    (unfold-single-defined-constant-globally $1)
    (unfold-single-defined-constant-globally subnet)
    simplify
    ))

(def-constant all%addresses
  "subnet(make%address(0#8,0#8,0#8,0#8),
          make%address(0#8,0#8,0#8,0#8))"
  (theory octets))

(def-theorem all-addresses-subnet-macete
  "all%addresses = indic{a:addresses,truth}" 
  (theory octets)
  (proof
   (

    (subnet-simplification all%addresses)

    )))

(def-constant all%class%a%addresses
  "lambda(o_1:octet, 
     subnet(make%address(o_1,0#8,0#8,0#8),
            make%address(255#8,0#8,0#8,0#8)))"
  (theory octets))

(def-theorem all-class-a-addresses-subnet-macete
  "forall(o_1:octet, 
     all%class%a%addresses(o_1) = indic{a:addresses, octet_1(a) = o_1})" 
  (theory octets)
  (proof
   (

    (subnet-simplification all%class%a%addresses)

    )))

(def-constant all%class%b%addresses
  "lambda(o_1,o_2:octet, 
     subnet(make%address(o_1,o_2,0#8,0#8),
            make%address(255#8,255#8,0#8,0#8)))"
  (theory octets))

(def-theorem all-class-b-addresses-subnet-macete
  "forall(o_1,o_2:octet, 
     all%class%b%addresses(o_1,o_2) 
      = 
     indic{a:addresses, octet_1(a) = o_1 and octet_2(a) = o_2})" 
  (theory octets)
  (proof
   (

    (subnet-simplification all%class%b%addresses)

    )))

(def-constant all%class%c%addresses
  "lambda(o_1,o_2,o_3:octet, 
     subnet(make%address(o_1,o_2,o_3,0#8),
            make%address(255#8,255#8,255#8,0#8)))"
  (theory octets))

(def-theorem all-class-c-addresses-subnet-macete
  "forall(o_1,o_2,o_3:octet, 
     all%class%c%addresses(o_1,o_2,o_3) 
      = 
     indic{a:addresses, 
       octet_1(a) = o_1 and octet_2(a) = o_2 and octet_3(a) = o_3})" 
  (theory octets)
  (proof
   (

    (subnet-simplification all%class%c%addresses)

    )))

(def-theorem single-address-to-subnet-specification
  "forall(a:addresses, 
     singleton{a} = subnet(a,make%address(255#8,255#8,255#8,255#8)))"
  (theory octets)
  (proof
   (

    direct-inference
    extensionality
    direct-inference
    (unfold-single-defined-constant-globally subnet)
    simplify
    (apply-macete-with-minor-premises equal-addresses-lemma)
    simplify

    )))

(def-constant all%protocols
  "indic{p:protocols,truth}"
  (theory single-filter-theory))

(def-constant all%ports
  "indic{p:protocols,truth}"
  (theory single-filter-theory))




