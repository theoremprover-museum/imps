(load-section basic-cardinality)

(def-language graph-language
  (embedded-language the-kernel-theory)
  (base-types vertices edges)
  (constants
   (endpoints "[edges -> sets[vertices]]")))

(def-theory graphs
  (language graph-language)
  (component-theories h-o-real-arithmetic)
  (axioms
   (edges-have-two-endpoints
    "forall(e:edges, forsome(v_1,v_2: vertices,
       endpoints(e) = singleton{v_1} union singleton{v_2}))")))

(def-theorem endpoints-is-total
  "total_q{endpoints,[edges -> sets[vertices]]}"
  (usages d-r-convergence)
  (theory graphs)
  (proof
   (

    insistent-direct-inference
    (instantiate-theorem edges-have-two-endpoints ("x_0"))

    )))

(def-constant loop
  "lambda(e:edges, singleton{endpoints(e)})"
  (theory graphs))

(def-constant parallel
  "lambda(e_1,e_2:edges, endpoints(e_1) = endpoints(e_2))"
  (theory graphs))

(def-constant adjacent%vertices
  "lambda(v_1,v_2:vertices, forsome(e:edges, 
     endpoints(e) = singleton{v_1} union singleton{v_2}))"
  (theory graphs))

(def-constant adjacent%edges
  "lambda(e_1,e_2:edges, forsome(v:vertices,
     v in endpoints(e_1)  and v in endpoints(e_2)))"
  (theory graphs))

(def-constant vertex%incidence%set
  "lambda(v:vertices, indic{e:edges, v in endpoints(e)})"
  (theory graphs))

(def-constant degree
  "lambda(v:vertices, f_card{vertex%incidence%set(v)})"
  (theory graphs))

(def-constant isolated
  "lambda(v:vertices, degree(v) = 0)"
  (theory graphs))