(comment 

 "Some simple examples of omissions in familiar proofs from high school
 geometry"


 "Possibly some examples of fallacious ``proofs'' that rely on diagrams"

 "General remarks about chess, and possibly about football ratings"

 "We will concentrate on the geometry in particular, and the general methodological 
approach.  We will not worry, at least at the beginning, about explaining the details 
behind the formal logic and automated theorem prover we will be using. We hope enough 
about this will be learned by osmosis. The student wil gradually become familiar with 
what we are doing, and may eventually be able to run the theorem prover by himself. ")

(comment 
 "The only primitive relation or function will be betweenness. That is, 
everything else will 
 be explained in terms of betweenness, with the use of a little set
 theory. For us, a geometry will be just a set together with a 3-place
 relation to be interpreted as the betweenness of the geometry. The
 elements of the set are the points. Here are some of the most basic 
 intuitive properties of
 betweenness, which we express as axioms. The first property states
 that if point b is between points a  and c, then b is also between c
 and a.  We use bet as the formal symbol for betweenness, and write
 bet(a,b,c) to mean that b is between a and c. Note that there is no 
 notion of distance here. Given two points, the distance between them 
 is not defined in this context.")

(def-language language-for-geometry
  (base-types points )
  (constants (bet "[points,points,points,prop]")))

(comment "This will take some explaining, especially the part about
 prop.")


(def-theory geometry-1
  (language language-for-geometry)
  (axioms
   (at-least-two-points
    "forsome(a,b:points, not(a=b))")
   (distinctness-1-2
    "forall(x,y,z:points, bet(x,y,z) implies not(x=y))")
   (distinctness-1-3
    "forall(x,y,z:points, bet(x,y,z) implies not(x=z))")
   (symmetry-of-betweeness
    "forall(x,y,z:points, bet(x,y,z)  iff bet(z,y,x))")
   (anti-cyclic
    "forall(x,y,z:points, bet(x,y,z) implies not(bet(y,x,z)))")
   (existence-left
    "forall(x,y:points, not x=y implies forsome(b:points, bet(b,x,y)))")
   (existence-middle
    "forall(x,y:points, not x=y implies forsome(a:points, bet(x,a,y)))")

   ))

(comment "Note that it would be enough in the symmetry axiom to have an 
implication
 instead of the equivalence. Below is an IMPS proof of this just in case.")

(comment "Anticipating an obvious question concerning the distinctness of 2nd and
  3rd arguments")


(def-theorem distinctness-2-3
  "forall(x,y,z:points, bet(x,y,z) implies not(y=z))"
  (theory geometry-1)
  (proof
   (
    (apply-macete-with-minor-premises symmetry-of-betweeness)
    direct-inference
    (instantiate-theorem distinctness-1-2 ("z" "y" "x"))
    simplify
    simplify
    )))

(comment

 (apply-macete-with-minor-premises symmetry-of-betweeness)
 (force-substitution "y=z" "z=y" (0))
 (block 
  (script-comment "`force-substitution' at (0)")
  (apply-macete-with-minor-premises distinctness-1-2)
  simplify)
 simplify

 )

(def-theorem existence-right
  "forall(x,y:points, not x=y implies forsome(c:points, bet(x,y,c)))"
  (theory geometry-1)
  (proof
   (


    (apply-macete-with-minor-premises symmetry-of-betweeness)
    (apply-macete-with-minor-premises existence-left)
    simplify

    )))

(comment "The terms left and right match the notation but have no geometric
content. However, the next theorem does have some content since it says that given any point, and any other point, the first point occurs between the second point and some other point.")

(def-theorem sandwich
  "forall(m:points,  forsome(x,y:points, bet(x,m,y)))"
  (theory geometry-1)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (instantiate-theorem at-least-two-points ())
    (antecedent-inference "with(p:prop,p);")
    (cut-with-single-formula "(not m=a) or (not m=b)")
    (move-to-sibling 1)
    simplify
    (block 
     (script-comment "node added by `cut-with-single-formula' at (0)")
     (antecedent-inference "with(p:prop,p or p);")
     (block 
      (script-comment "node added by `antecedent-inference' at (0)")
      (instantiate-theorem existence-right ("a" "m"))
      auto-instantiate-existential)
     (block 
      (script-comment "node added by `antecedent-inference' at (1)")
      (instantiate-theorem existence-right ("b" "m"))
      auto-instantiate-existential))


  

    )))

(comment "We now define what should correspond to our intuitive notion 
of collinearity.")



(def-constant coll
  "lambda(x,y,z:points, bet(x,y,z) or bet(y,x,z) or bet(x,z,y))"
  (theory geometry-1)
  
  )

(comment "Notice that this definition is really just an abbreviation.
 We are defining the concept of collinearity in terms of the concept of
 betweeness. Notice also that collinearity is a weaker notion
 than betweeness.")

(comment "There are of course 6 betweenness assertions we could have
 included here, and we only used 3. That is because of the
 symmetry-of-betweeness axiom. This version has the advantage that often we will only have to consider ythree cases instead of six.))

(comment "We should not be surprised that we can now prove the following
group of simple theorems. In fact, if we could not prove them, we would know 
something was wrong. Perhaps our definition was wrong, or we needed
more axioms.")

(def-theorem collinear-all-cases
  "forall(x,y,z:points, coll(x,y,z) iff (bet(x,y,z) or bet (z,y,x) or
      bet(y,x,z) or bet(z,x,y) or bet(x,z,y) or bet(y,z,x)))"
  (theory geometry-1)
  (proof
   (
    (unfold-single-defined-constant (0) coll)
    direct-and-antecedent-inference-strategy
    (block 
     (script-comment "`direct-and-antecedent-inference-strategy' at (0 1 0 1)")
     (contrapose "with(z,y,x:points,not(bet(x,y,z)));")
     (apply-macete-with-minor-premises symmetry-of-betweeness))
    (block 
     (script-comment "`direct-and-antecedent-inference-strategy' at (0 1 0
3)")
     (contrapose "with(z,x,y:points,not(bet(y,x,z)));")
     (apply-macete-with-minor-premises symmetry-of-betweeness))
    (apply-macete-with-minor-premises symmetry-of-betweeness)

    )))


(def-theorem coll-disjunctive-permuter 
  "forall(a,b,c:points, 
    coll(a,b,c) iff 
    (coll(a,b,c) or 
     coll(a,c,b) or 
     coll(b,a,c) or 
     coll(b,c,a) or 
     coll(c,a,b) or
     coll(c,b,a)))"
  (theory geometry-1)
  (proof
   (

    (apply-macete-with-minor-premises collinear-all-cases)
    direct-and-antecedent-inference-strategy

    )))

(comment "Here are some exercises that we will need late to do specific
 ``flipping'' around. The proofs are now completely trivial since the
 theorem collinear-all-cases is doing all the work for us.")

(def-theorem collinear-flipper-1-2
  "forall(x,y,z:points, coll(x,y,z) iff coll(y,x,z))"
  (theory geometry-1)

  (proof(
	 (apply-macete-with-minor-premises collinear-all-cases)
	 direct-and-antecedent-inference-strategy
	 
	 ) ))


(def-theorem collinear-flipper-2-3
  "forall(x,y,z:points, coll(x,y,z) iff coll(x,z,y))"
  (theory geometry-1)
  (proof

   (
   
    (apply-macete-with-minor-premises collinear-all-cases)
    direct-and-antecedent-inference-strategy

    ) ))


(def-theorem collinear-flipper-1-3
  "forall(x,y,z:points, coll(x,y,z) iff coll(z,y,x))"
  (theory  geometry-1)
  (proof
   (
    (apply-macete-with-minor-premises collinear-all-cases)
    direct-and-antecedent-inference-strategy
    )))




(def-theory geometry-2
  (language geometry-1)
  (component-theories geometry-1)
  (axioms
   
   (switching
    "forall(x,y,a,b:points, not a=b and
         coll(x,y,a) and coll(x,y,b) implies coll(a,b,x))")

   ))

(comment "By now, it should not be surprising that it was no restriction in
the switching axiom to consider only the first point a.  Let's prove this as 
an exercise.")

(def-theorem other-switching
  "forall(x,y,a,b:points, not a=b and coll(x,y,a) and coll(x,y,b) implies coll(a,b,y))"
  (theory geometry-2)
  (proof
   (
    
    (apply-macete-locally-with-minor-premises collinear-flipper-1-2
					      (0)
					      "coll(x,y,a)")
    (apply-macete-locally-with-minor-premises collinear-flipper-1-2
					      (0)
					      "coll(x,y,b)")
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises switching)
    auto-instantiate-existential

  

    )))


(def-theorem switching-all-cases
  "forall(a,b,c:points, forsome(x:points, 
        not b=c and coll(a,x,b) and coll(a,x,c)
					 or
        not c=a and coll(b,x,c) and coll(b,x,a)
					 or
        not a=b and coll(c,x,a) and coll(c,x,b))
                        implies
                       coll(a,b,c))"
  (theory geometry-2)
  (proof
   (


    direct-inference
    direct-inference
    (contrapose "with(p:prop,p);")
    (apply-macete-with-minor-premises coll-disjunctive-permuter)
    (contrapose "with(p:prop,p);")
    (antecedent-inference "with(p:prop,p);")
    (antecedent-inference "with(p:prop,p);")
    (block 
     (script-comment "`antecedent-inference' at (0)")
     (apply-macete-with-minor-premises collinear-flipper-1-3)
     (apply-macete-with-minor-premises switching)
     (instantiate-existential ("x"))
     simplify
     (apply-macete-with-minor-premises coll-disjunctive-permuter)
     (apply-macete-with-minor-premises coll-disjunctive-permuter))
    (block 
     (script-comment "`antecedent-inference' at (1)")
     (apply-macete-with-minor-premises collinear-flipper-2-3)
     (apply-macete-with-minor-premises switching)
     (instantiate-existential ("x"))
     simplify
     (apply-macete-with-minor-premises coll-disjunctive-permuter)
     (apply-macete-with-minor-premises coll-disjunctive-permuter))
    (block 
     (script-comment "`antecedent-inference' at (2)")
     (apply-macete-with-minor-premises switching)
     (instantiate-existential ("x"))
     (apply-macete-with-minor-premises coll-disjunctive-permuter)
     (apply-macete-with-minor-premises coll-disjunctive-permuter))   

    )))

(def-theorem triple-switching
  "forall(a,b,c,x,y:points, 
    not(a=b) and not a=c and not b=c 
      implies
    coll(x,y,a) and coll(x,y,b) and coll(x,y,c) implies coll(a,b,c))"
  (theory geometry-2)
  (proof
   (
    
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises switching)
    (apply-macete-with-minor-premises collinear-flipper-2-3)
    (instantiate-existential ("x"))
    (block 
     (script-comment "`instantiate-existential' at (0 1)")
     (apply-macete-with-minor-premises switching)
     auto-instantiate-existential
     simplify)
    (block 
     (script-comment "`instantiate-existential' at (0 2)")
     (apply-macete-with-minor-premises switching)
     auto-instantiate-existential
     simplify)

    )))

(def-constant coll_set
  "lambda(s:sets[points],
           forall(x,y,z:points,x in s and y in s and z in s and not x=y
 and not x=z and not y=z 
 implies coll(x,y,z)))"
  (theory geometry-2))


