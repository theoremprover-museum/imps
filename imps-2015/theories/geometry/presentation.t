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

(include-files
  (files (imps theories/geometry/sets))
  )

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

(def-theorem implication-equivalent
  "forall(p:[points,points,points->prop],
   forall(x,y,z:points,
    p(x,y,z) implies p(z,y,x)) iff
   forall(x,y,z:points,  p(x,y,z) iff p(z,y,x)))"
  (theory geometry-1)
  (proof
   (
    (prove-by-logic-and-simplification 0)
    )))

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

(def-theorem between-implies-collinear-contra
  "forall(a,b,c:points, not(coll(a,b,c)) implies not(bet(a,b,c)))"
  (theory geometry-1)
  (proof
   (

    (unfold-single-defined-constant (0) coll)
    simplify
    )))

(comment "Notice that this definition is really just an abbreviation.
 We are defining the concept of collinearity in terms of the concept of
 betweeness. Notice also that collinearity is a weaker notion
 than betweeness.")

(comment "There are of course 6 betweenness assertions we could have
 included here, and we only used 3. That is because of the
 symmetry-of-betweeness axiom. This version has the advantage that often we will only have to consider ythree cases instead of six." )

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

(def-theorem coll-conjunctive-permuter 
  "forall(a,b,c:points, 
    coll(a,b,c) iff 
    (coll(a,b,c) and 
     coll(a,c,b) and 
     coll(b,a,c) and 
     coll(b,c,a) and 
     coll(c,a,b) and
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

(comment "What we observe next is that if points are collinear according
 to our definition, then they are distinct.  We do one case explicitly and
depend on flippers for the others.")


(def-theorem collinear-implies-distinct-lemma
  "forall(x,y,z:points,coll(x,y,z) implies not x=y)"
  (theory geometry-1)
  (proof
   (
    
    unfold-defined-constants
    direct-and-antecedent-inference-strategy
    (block 
     (script-comment "`direct-and-antecedent-inference-strategy' at (0 0 0)")
     (apply-macete-with-minor-premises distinctness-1-2)
     auto-instantiate-existential)
    (block 
     (script-comment "`direct-and-antecedent-inference-strategy' at (0 0 1)")
     (force-substitution "x=y" "y=x" (0))
     (block 
      (script-comment "`force-substitution' at (0)")
      (apply-macete-with-minor-premises distinctness-1-2)
      auto-instantiate-existential)
     simplify)
    (block 
     (script-comment "direct-and-antecedent-inference-strategy' at (0 0 2)")
     (apply-macete-with-minor-premises distinctness-1-3)
     auto-instantiate-existential)
   
    
    )))


(comment "We will give two proofs of the next result. First a beginners
  style proof, and then a more expert style proof. It is not necessary 
  to follow all of this now, but you may start to develop a picture of 
  what is going on in IMPS proofs.")



(def-theorem collinear-implies-distinct
  "forall(x,y,z:points,coll(x,y,z) implies not x=y and not y=z and not x=z)"
  (theory geometry-1)
  (proof
   (
    
    direct-and-antecedent-inference-strategy
    (block 
     (script-comment "node added by `direct-and-antecedent-inference-strategy' at (0 0 0)")
     (apply-macete-with-minor-premises collinear-implies-distinct-lemma)
     auto-instantiate-existential)
    (block 
     (script-comment "node added by `direct-and-antecedent-inference-strategy' at (0 0 1)")
     (incorporate-antecedent "with(z,y,x:points,coll(x,y,z));")
     (apply-macete-with-minor-premises collinear-flipper-1-2)
     (apply-macete-with-minor-premises collinear-flipper-2-3)
     (apply-macete-with-minor-premises collinear-implies-distinct-lemma)
     direct-inference
     auto-instantiate-existential)
    (block 
     (script-comment "node added by `direct-and-antecedent-inference-strategy' at (0 0 2)")
     (incorporate-antecedent "with(z,y,x:points,coll(x,y,z));")
     (apply-macete-with-minor-premises collinear-flipper-2-3)
     (apply-macete-with-minor-premises collinear-implies-distinct-lemma)
     direct-inference
     auto-instantiate-existential)


  

    )) )

(comment "expert level proof saves work."

  (apply-macete-with-minor-premises collinear-implies-distinct-lemma)
    direct-and-antecedent-inference-strategy
    auto-instantiate-existential
    (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (0 0 1 0)")
      (instantiate-existential ("x"))
      (apply-macete-with-minor-premises collinear-flipper-1-3)
      (apply-macete-with-minor-premises collinear-flipper-2-3))
    (instantiate-existential ("y")) 
)

(comment "We have not yet stated enough axioms to conclude very much about
betweenness or collinearity. For example, we would certainly want the
 following to be the case: If point x is collinear with points a and b,
 and point y is also collinear with a and b, then a is collinear with x and y.
Suppose we take betweeness as follows: between(x,y,z) means that y is the
midpoint of segment xz, with x and z distinct. The points may come from a line 
or a Euclidean plane, etc, it does not matter. Then, it is easy to check that
all of the above axioms hold. (It would be a nice exercise to actually prove 
this via an IMPS interpretation.) However, the property we mentioned above does
not. For example, we have bet(0,1,2) so coll(1,2,0). Also bet(1,2,3), so
coll(1,2,3). But it is easy to check that coll(2,3,0) does not hold since  
none of the three points is the midpoint of the other two.")

(comment "So we go ahead and introduce just what we said above. This may seem 
like cheating, but it isn't really. You have to make some assumptions, and this
particular one is satisfied in our most familiar models of geometry, and so is
extremely unlikely to cause an inconsistency. Moreover, we are not requiring
anything beyond what we intuitively want anyway.")

  
(comment "Notice that we could have stated the switching axiom directly in
 terms of betweeness, but that would have been more cumbersome. More
 importantly, the statement is really about the weaker notion of
 collinearity.")


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

(comment
 "collinear-killer is used to ground assertions of the form
  coll(a,b,c) that can be grounded with one application of switching
  together with collinear-flippers")

(def-script bet-replacer 0
  (
   (while (matches? "with(p:prop, p)"
		    "with(x,y,z:points, bet(x,y,z))")
	  (block
	   (contrapose "with(x,y,z:points, bet(x,y,z))")
	   (apply-macete-with-minor-premises between-implies-collinear-contra)
	   (apply-macete-with-minor-premises coll-conjunctive-permuter)
	   (contrapose 0))
	  (skip))

   ))

(def-script coll-replacer 0
  (
   (while (matches? "with(p:prop, p)"
		    "with(x,y,z:points, coll(x,y,z))")
	  (block
	   (contrapose "with(x,y,z:points, coll(x,y,z))")
	   (apply-macete-with-minor-premises coll-conjunctive-permuter)
	   (contrapose 0))
	  (skip))

   ))

(def-script inequality-killer 0
  (

   bet-replacer
   coll-replacer
   (label-node here)
   (antecedent-inference-strategy (* "with(p:prop, p)"))
   direct-and-antecedent-inference-strategy
   (jump-to-node here)
   (for-nodes
    (unsupported-descendents)
	      
    (if (matches? "with(x,y:points, not x=y)"
		  "with(x,y,z:points, coll(x,y,z))")
	(block
	 (apply-macete-with-minor-premises collinear-implies-distinct-lemma)
	 auto-instantiate-existential)
	(skip)))))

(def-script collinear-killer 1
  ( (let-script inequality-killer 0
  (

   (label-node here)
   (antecedent-inference-strategy (* "with(p:prop, p)"))
   direct-and-antecedent-inference-strategy
   (jump-to-node here)
   (for-nodes
    (unsupported-descendents)
	      
    (if (matches? "with(x,y:points, not x=y)"
		  "with(x,y,z:points, coll(x,y,z))")
	(block
	 (apply-macete-with-minor-premises collinear-implies-distinct-lemma)
	 auto-instantiate-existential)
	(skip)))))
    (cut-with-single-formula "with(tt:points,tt=tt)")
    (antecedent-inference-strategy (* "with(p:prop, p)"))
    bet-replacer
    coll-replacer
    (antecedent-inference-strategy (* "with(p:prop, p)"))
    (apply-macete-with-minor-premises switching-all-cases)
    (label-node here)
    (instantiate-existential ($1))
    (jump-to-node here)
    (move-to-descendent (0 0))
    (label-node there-2)
    (for-nodes (unsupported-descendents) $inequality-killer)
    (jump-to-node there-2)
    (contrapose 0)
    (for-nodes (unsupported-descendents) $inequality-killer)
    (jump-to-node there-2)
    (contrapose 1)
    (for-nodes (unsupported-descendents) $inequality-killer)
    (jump-to-node here)
    (prove-by-logic-and-simplification 0)  
))
 
(comment 
 (def-script collinear-killer 1
   ( (let-script inequality-killer 0
		 (

		  (label-node here)
		  (antecedent-inference-strategy (* "with(p:prop, p)"))
		  direct-and-antecedent-inference-strategy
		  (jump-to-node here)
		  (for-nodes
		   (unsupported-descendents)
	      
		   (if (matches? "with(x,y:points, not x=y)"
				 "with(x,y,z:points, coll(x,y,z))")
		       (block
			(apply-macete-with-minor-premises collinear-implies-distinct-lemma)
			auto-instantiate-existential)
		       (skip)))))
     (cut-with-single-formula "with(tt:points,tt=tt)")
     (antecedent-inference-strategy (* "with(p:prop, p)"))
     bet-replacer
     coll-replacer
     (antecedent-inference-strategy (* "with(p:prop, p)"))
     (apply-macete-with-minor-premises switching-all-cases)
     (label-node here)
     (instantiate-existential ($1))
     (label-node there)
     (prove-by-logic-and-simplification 0)
    
     (jump-to-node there)
     (for-nodes (unsupported-descendents) $inequality-killer)
     (jump-to-node here)
     (prove-by-logic-and-simplification 0)  
     )))

(comment "If our switching axiom is strong enough to get the job done,
 then we should also be able to handle three points at a time as in
 the following result.")

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

;;(comment "Using the killer
;;direct-and-antecedent-inference-strategy
;;(apply-macete-with-minor-premises switching)
;;(apply-macete-with-minor-premises collinear-flipper-2-3)
;;(instantiate-existential (x))
;;(collinear-killer y)
;;(collinear-killer y)")

(def-script collinear-triple-killer 2
  (
   (let-script
    bet-replacer 0
    (
     (while (matches? "with(p:prop, p)"
		      "with(x,y,z:points, bet(x,y,z))")
	    (block
	     (contrapose "with(x,y,z:points, bet(x,y,z))")
	     (apply-macete-with-minor-premises between-implies-collinear-contra)
	     (apply-macete-with-minor-premises coll-conjunctive-permuter)
	     (contrapose 0))
	    (skip))

     ))

   (let-script
    coll-replacer 0
    (
     (while (matches? "with(p:prop, p)"
		      "with(x,y,z:points, coll(x,y,z))")
	    (block
	     (contrapose "with(x,y,z:points, coll(x,y,z))")
	     (apply-macete-with-minor-premises coll-conjunctive-permuter)
	     (contrapose 0))
	    (skip))

))


	   

    (antecedent-inference-strategy (* "with(p:prop, p)"))
    $bet-replacer
    $coll-replacer
    (antecedent-inference-strategy (* "with(p:prop, p)"))
    (apply-macete-with-minor-premises triple-switching)
    (label-node here)
    (instantiate-existential ($2)
    (label-node there)
    (prove-by-logic-and-simplification 0)
    (jump-to-node there)
    (for-nodes (unsupported-descendents) inequality-killer)
    (jump-to-node here)
    (prove-by-logic-and-simplification 0))))

(comment "Our objective is to formulate an appropriate definition of line.
  At the very least, a line should be a set of points such that any three
distinct points in the set are collinear. With this in mind, we formulate the 
following definition, which will not capture the full intuitive concept,
but which will express an important constituent notion.")


(def-constant coll_set
  "lambda(s:sets[points],
           forall(x,y,z:points,x in s and y in s and z in s and not x=y
 and not x=z and not y=z 
 implies coll(x,y,z)))"
  (theory geometry-2))

(comment "While, according to our intuition, not every collinear set
 should be a line, every line should be a collinear set.")

(comment "Let's experiment a bit with this concept and identify some colinear
sets.")

(def-theorem singletons-are-collinear
  "forall(x:points, coll_set(singleton{x}))"
  (theory geometry-2)
  (proof
   (

    (unfold-single-defined-constant-globally coll_set)
    simplify

    )))

(def-theorem pairs-are-collinear
  "forall(x,y:points, coll_set(indic{z:points,z=x or z=y}))"
  (theory geometry-2)
  (proof
   (

    (unfold-single-defined-constant-globally coll_set)
    (prove-by-logic-and-simplification 0)
    )))

(comment "Here we used the heavier duty command
 prove-by-logic-and-simplification instead of just simplfy, because we had
 a more complicated expression.")

(comment "Next we introduce a more interesting set which will also turn out
  to be collinear. We will define segments, specifically, open segments that
  do not contain their endpoints.")

(def-constant seg
  "lambda(a,b:points,if( not a=b,indic{p:points,bet(a,p,b)},?sets[points]))"
  (theory geometry-2)
  )

(def-theorem segments-are-collinear
  "forall(a,b:points,not a=b implies coll_set(seg(a,b)))"
  (theory geometry-2)
  (proof 
   (
    unfold-defined-constants
    simplify
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises triple-switching)
    (apply-macete-with-minor-premises collinear-all-cases)
    (instantiate-existential ("b" "a"))
    )
   ))

(comment "We now introduce the notion of a line as a maximal collinear set
  of points.")

(def-constant line
  "lambda(l:sets[points], 
             coll_set(l) and 
             forall(s:sets[points], 
                     coll_set(s) and l subseteq s  implies l = s))"
  (theory geometry-2))

(comment "Next we suggest a more concrete looking notion, that would be 
  another natural contender for the basic definition of line. Eventually,
  we will show that these two definitions are essentially equivalent. This will
  give us added confidence that we have found, if not the correct notion, at
 least an important notion, a sort of validation by robustness.")

(def-constant le
  "lambda (x,y:points, 
      if(not x=y, indic{p:points, p=x or p=y or coll(x,y,p)} ,?sets[points]))"
  (theory geometry-1)
  )

(comment "The next theorem is needed for tchnical reasons. It will make some
 proofs more streamlined by having certain things done automatically by IMPS.")
 


(def-theorem definedness-of-le
  "forall(a,b:points,not a=b implies #(le(a,b)))"
  (theory geometry-2)
  (usages d-r-convergence)
  (proof 
   (
    unfold-defined-constants
    simplify

    )))

(comment "This is an attempt to define the line determined by the points x
  and y, for x and y distinct. Of course, we are yet to validate this
  approach.For example, it is not clear that le(a,b) is a collinear set.
 However, it should be fairly clear that le(a,b) must contain at least three
  points under this definition, namely a, b, and any point between a and b,
 of which there must be at least one, by the existence-middle axiom. You can
 get two more points by using the existence-left axiom and the existence-
 right theorem.  Let us try to show that a line, under the first definition,
 must contain at least two points. We will need this result later on.")

(comment "Notice that the definition of le(a,b) tells us which elements
  belong to the set le(a,b). We say that le(a,b) is defined extensionally.
  On the other hand, our concept of line says that a line is a set that
  satisfies a certain property.")


(comment "The next little lemma is entirely trivial. Its purpose is purely 
 technical, and we would not even think about this if we were not doing things
 formally.  It will allow us to cut down on the number of cases we need to
  consider.")

(def-theorem other-point-lemma
  "forall(x:points, forsome(y:points,not x=y))"
  (theory geometry-1)
  (proof
   (
    (instantiate-theorem at-least-two-points ())
    (antecedent-inference "with(p:prop,p);")
    direct-and-antecedent-inference-strategy
    (case-split ("x=a"))
    (block 
     (script-comment "node added by `case-split' at (1)")
     (instantiate-existential ("b"))
     simplify)
    (instantiate-existential ("a"))
    )))

(def-theorem lines-contain-two-points
  "forall(l:sets[points], 
               line(l)
                   implies
               forsome(a,b:points, a in l and b in l and not(a=b)))"
  (theory geometry-2)
  (proof
   (


    unfold-defined-constants
    direct-and-antecedent-inference-strategy
    (case-split ("forall(p:points, not p in l)"))
    (block 
     (script-comment "`case-split' at (1)")
     (instantiate-theorem at-least-two-points ())
     (cut-with-single-formula "coll_set(indic{z:points,z=a or z=b})")
     (move-to-sibling 1)
     (apply-macete-with-minor-premises pairs-are-collinear)
     (block 
      (script-comment "`cut-with-single-formula' at (0)")
      (auto-instantiate-universal-antecedent "with(l:sets[points],
  forall(s:sets[points],
    coll_set(s) and l subseteq s implies l=s));")
      empty-set-handler
      empty-set-handler))
    (block 
     (script-comment "`case-split' at (2)")
     pick-an-element
     (case-split ("forsome(q:points, not p = q and q in l)"))
     (block 
      (script-comment "`case-split' at (1)")
      (antecedent-inference "with(p:prop,forsome(q:points,p));")
      auto-instantiate-existential)
     (block 
      (script-comment "`case-split' at (2)")
      (cut-with-single-formula "forsome(r:points, not(p=r))")
      (move-to-sibling 1)
      (apply-macete-with-minor-premises other-point-lemma)
      (block 
       (script-comment "`cut-with-single-formula' at (0)")
       (antecedent-inference "with(p:prop,forsome(r:points,p));")
       (cut-with-single-formula "coll_set(indic{x:points, x=p or x=r})")
       (move-to-sibling 1)
       (apply-macete-with-minor-premises pairs-are-collinear)
       (block 
	(script-comment "`cut-with-single-formula' at (0)")
	(auto-instantiate-universal-antecedent "with(l:sets[points],
  forall(s:sets[points],
    coll_set(s) and l subseteq s implies l=s));")
	(block 
	 (script-comment "`auto-instantiate-universal-antecedent' at (0 0 0 1 0 0)")
	 indic-removal
	 (contrapose "with(p:prop,not(forsome(q:points,p)));")
	 (instantiate-existential ("x_$0"))
	 simplify)
	(block 
	 (script-comment "`auto-instantiate-universal-antecedent' at (0 0 1)")
	 (instantiate-existential ("p " "r"))
	 indic-handler))))))))


(comment "Notice that it is not automatically the case that
 le(a,b)=le(b,a). If this weren't the case clearly something would be wrong, 
 since we are hoping that le(a,b) will correspond to ``the line determined  by a and b''  which doesn't depend on the order of a and b. Let's pause to check 
this out.")

(comment "We write  le(a,b)==le(b,a) instead of  le(a,b)=le(b,a) to include the
 assertion that one side is defined if and only if the other is, as well as
 the assertion that if both sides are defined, they are equal.")

(def-theorem le-is-symmetric
  "forall(a,b:points, le(a,b)==le(b,a))"
  (theory geometry-1)
  (proof
   (


    (unfold-single-defined-constant-globally le)
    direct-and-antecedent-inference-strategy
    (case-split ("a=b"))
    simplify
    (block 
     (script-comment "node added by `case-split' at (2)")
     simplify
     (apply-macete-locally collinear-flipper-1-2 (0) "coll(a,b,p)")
     indic-equality


 
     ))))

(comment "We now show that a set of the form le(a,b) is a line. As a first step
  we show that le(a,b) is a collinear set. The basic idea in the proof is to
  choose 3 distinct points in le(a,b) and show that they are collinear. There
  will be anumber of cases to consider depending upon which of those points
  happen to be either a or b. However, most of the hard work has really been
  done already. We will just need to make sure that we haven't left out any
  cases.  IMPS will do this for us.")


(def-theorem le-is-collinear
  "forall(a,b:points, not a=b implies coll_set(le(a,b)))"
  (theory geometry-2)
  (proof
   (
    unfold-defined-constants
    simplify
    big-d-with-simplification
    (apply-macete-with-minor-premises collinear-flipper-1-3)
    (block 
     (script-comment "node added by `big-d-with-simplification' at (0 0 0 0 0 0 2 1 0)")
     (apply-macete-with-minor-premises collinear-flipper-1-3)
     (apply-macete-with-minor-premises collinear-flipper-2-3))
    (block 
     (script-comment "node added by `big-d-with-simplification' at (0 0 0 0 0 0 2 2 0)")
     (apply-macete-with-minor-premises switching)
     auto-instantiate-existential)
    (block 
     (script-comment "node added by `big-d-with-simplification' at (0 0 0 0 0 1 0 2 0)")
     (apply-macete-with-minor-premises collinear-flipper-1-3)
    (apply-macete-with-minor-premises collinear-flipper-1-2))
    (apply-macete-with-minor-premises collinear-flipper-2-3)
    (block 
     (script-comment "node added by `big-d-with-simplification' at (0 0 0 0 0 1 2 2 0)")
     (apply-macete-with-minor-premises other-switching)
     auto-instantiate-existential)
    (apply-macete-with-minor-premises collinear-flipper-1-2)
    (block 
     (script-comment "node added by `big-d-with-simplification' at (0 0 0 0 0 2 0 2 0)")
     (apply-macete-with-minor-premises collinear-flipper-2-3)
     (apply-macete-with-minor-premises switching)
     (instantiate-existential ("b")))
    (block 
     (script-comment "node added by `big-d-with-simplification' at (0 0 0 0 0 2 1 2 0)")
     (apply-macete-with-minor-premises collinear-flipper-2-3)
     (apply-macete-with-minor-premises other-switching)
     auto-instantiate-existential)
    (block 
     (script-comment "node added by `big-d-with-simplification' at (0 0 0 0 0 2 2 0 0)")
     (apply-macete-with-minor-premises collinear-flipper-1-3)
     (apply-macete-with-minor-premises switching)
     auto-instantiate-existential
     simplify)
    (block 
     (script-comment "node added by `big-d-with-simplification' at (0 0 0 0 0 2 2 1 0)")
     (apply-macete-with-minor-premises collinear-flipper-1-3)
     (apply-macete-with-minor-premises other-switching)
     (instantiate-existential ("a"))
     simplify)
    (block 
     (script-comment "node added by `big-d-with-simplification' at (0 0 0 0 0 2 2 2)")
     (apply-macete-with-minor-premises triple-switching)
     auto-instantiate-existential)

    )))


(def-theorem le-is-a-line
  "forall(a,b:points, not a=b implies line(le(a,b)))"
  (theory geometry-2)
  (proof
   (

    (unfold-single-defined-constant (0) line)
    (apply-macete-with-minor-premises le-is-collinear)
    (apply-macete-with-minor-premises tr%subseteq-antisymmetry)
    (unfold-single-defined-constant-globally coll_set)
    direct-and-antecedent-inference-strategy
    (incorporate-antecedent "with(s,f:sets[points],f subseteq s);")
    simplify-insistently
    (unfold-single-defined-constant-globally le)
    simplify-insistently
    direct-and-antecedent-inference-strategy
    (backchain "with(p:prop,forall(x,y,z:points,p));")
    simplify

    )))



(comment "Exercise: There is another approach to proving that le(a,b) is
  a collinear set. It is somewhat more elegant and is based on the following
  general result.

(def-theorem extending-collinear-sets
  forall(x:points,s:sets[points], coll_set(s) and 
  forsome(a,b:points, a in s and b in s and coll(a,b,x)) 
   implies coll_set(s union singleton{x}))
  (theory geometry-2)

 This theorem says that if you start with a collinear set s and if some
 element x (outside the set is the interesting case) is collinear with any two
 particular elements of s, then it is collinear with any two elements of s
 and thus if it is added to s, the resulting set is still collinear.

 Using this result, we can obtain the collinearity of of le(a,b) by adding
 one at a time  to {a,b} all the elements collinear with a and b.  This
 argument is intuitively clear, but requires some set theoretic apparatus
 that we do not want to develop at this point.")
 

 




(comment "We now show that every line is of the form le(a,b), in fact, of 
 the form  le(a,b) for any distinct points a, b in the line. We have already
 shown that a line contains at least two points, so we will now have an
 explicit  way of describing any particular line extensionally.")

(def-theorem lines-are-le
  "forall(s:sets[points],a,b:points, 
                          line(s) and a in s and b in s and not(a=b)
                            implies
                          s = le(a,b))"
  (theory geometry-2)
  (proof
   (


    (unfold-single-defined-constant (0) line)
    direct-and-antecedent-inference-strategy
    (incorporate-antecedent "with(s:sets[points],coll_set(s));")
    unfold-defined-constants
    simplify
    (apply-macete-with-minor-premises tr%subseteq-antisymmetry)
    simplify-insistently
    big-d-with-simplification
    (instantiate-universal-antecedent "with(p:prop,forall(s_$0:sets[points],p));"
				      ("le(a,b)"))
    (block 
     (script-comment "node added by `instantiate-universal-antecedent' at (0 0 0 0)")
     (contrapose "with(f:sets[points],not(coll_set(f)));")
     (apply-macete-with-minor-premises le-is-collinear))
    (block 
     (script-comment "node added by `instantiate-universal-antecedent' at (0 0 0 1 0 0)")
     (contrapose "with(x_$0:points,f:sets[points],not(x_$0 in f));")
     (unfold-single-defined-constant (0) le)
     simplify)
    (block 
     (script-comment "node added by `instantiate-universal-antecedent' at (0 0 1)")
     (incorporate-antecedent "with(f,s:sets[points],s=f);")
     (unfold-single-defined-constant (0) le)
     simplify
     direct-and-antecedent-inference-strategy
     (backchain "with(f,s:sets[points],s=f);")
     (weaken (0))
     simplify-insistently)
    (block 
     (script-comment "node added by `instantiate-universal-antecedent' at (1 1 0)")
     (unfold-single-defined-constant (0) le)
     simplify)
    )))

(comment "We now introduce still another approach for defining lines.  This
 approach is very general, and will be useful in defining planes or even
 spaces of higher dimension.")

(def-constant coll%closed
  "lambda(s:sets[points], forall(a,b,x:points, 
                            a in s and b in s  and coll(a,b,x)
                              implies
                            x in s))"
  (theory geometry-2))

(comment "If we replaced the coll(a,b,x) with bet(a,x,b) we would have instead
 a concept called convexity. Notice that a set s is coll%closed just in case
 whenever two points are in s, then the line that they determine is a subset
 of s.  Let's prove that as an easy exercise.")

(def-theorem coll%closed-closed-under-le
  "forall(b,a:points,u:sets[points], 
             a in u and b in u and coll%closed(u) and not a=b
              implies 
             le(a,b) subseteq u)"
  (theory geometry-2)
  (proof
   (

    unfold-defined-constants
    simplify-insistently
    big-d-with-simplification
    (backchain "with(p:prop,forall(x:points,p));")
    (instantiate-existential ("b" "a"))

    )))


(comment "Now we introduce the important notion of collinear closure. There are
  two equivalent ways of doing this. One can build the closure up via 
  iteration.  On the other hand one can take the closure to be the smallest
  set closed uner collinearity, which can easily be shown to be the
 intersection of all sets closed under collinearity. In this case, one must 
 show that there is a least one set closed under collineariy. This will be
 asy to do. We have chosen the second approach as being more convenient for
 our immediate needs. It would be interesting to develop the first method for
 later use.")
    

(def-constant coll%closure
  "lambda(s:sets[points], 
          iota(t:sets[points], 
                coll%closed(t) and s subseteq t and 
                forall(u:sets[points], 
                   coll%closed(u) and s subseteq u implies t subseteq u)))"
  (theory geometry-2))


(comment "The next result, which is just a special case of a much more general
  result with same proof, relates  coll%closure and coll%closed. Notice first
 that coll%closure denotes a set while coll%closed is a predicate.")

(def-theorem coll%closed-iff-fixed-under-coll%closure
  "forall(s:sets[points],coll%closed(s) iff coll%closure(s)=s)"
  (theory geometry-2)
  reverse
  (proof
   (
    (unfold-single-defined-constant (0) coll%closure)
    direct-and-antecedent-inference-strategy
    (block 
     (script-comment "node added by `direct-and-antecedent-inference-strategy' at (0 0)")
     (apply-macete-with-minor-premises eliminate-iota-macete)
     direct-and-antecedent-inference-strategy
     (apply-macete-with-minor-premises tr%subseteq-antisymmetry)
     direct-and-antecedent-inference-strategy
     simplify)
    (block 
     (script-comment "node added by `direct-and-antecedent-inference-strategy' at (0 1)")
     (contrapose "with(p:prop,p);")
     (apply-macete-with-minor-premises eliminate-iota-macete)
     simplify))))


(comment "Add an exercise to do this in th abstract, for closure under
 arbitrary relations of some number of places.")

(comment "Let's compute the collinear closure of some basic sets.")

(def-theorem emptyset-is-coll%closed
  "coll%closed(empty_indic{points})"
  (theory geometry-2)
  (proof
   (


    (unfold-single-defined-constant (0) coll%closed)
    simplify
    )))

(def-theorem emptyset-equals-its-coll%closure
  "coll%closure(empty_indic{points})=empty_indic{points}"
  (theory geometry-2)
  (proof
   (
    (apply-macete-with-minor-premises
     rev%coll%closed-iff-fixed-under-coll%closure)
    (apply-macete-with-minor-premises emptyset-is-coll%closed)

    )))




(def-theorem universe-is-coll%closed
  "coll%closed(sort_to_indic{points})"
  (theory geometry-2)
  (proof
   (


    (unfold-single-defined-constant (0) coll%closed)
    simplify
    )))

(def-theorem universe-equals-its-coll%closure
  "coll%closure(sort_to_indic{points})=sort_to_indic{points}"
  (theory geometry-2)
  (proof
   (
    (apply-macete-with-minor-premises
     rev%coll%closed-iff-fixed-under-coll%closure)
    (apply-macete-with-minor-premises universe-is-coll%closed)

    )))


(comment "This last one about singletons is just a ``technicality''. The
 previous proofs were essentially identical. This one is a bit more 
 complicated")

(def-theorem singleton-is-coll%closed
  "forall(x:points, coll%closed(singleton{x}))"
  (theory geometry-2)
  (proof
   (

    (unfold-single-defined-constant (0) coll%closed)
    simplify
    direct-and-antecedent-inference-strategy
    (instantiate-theorem collinear-implies-distinct ("x" "x" "x_$0"))

    )))

(def-theorem singleton-equals-its-coll%closure
  "forall(x:points,coll%closure(singleton{x})=singleton{x})"
  (theory geometry-2)
  (proof
   (
    (apply-macete-with-minor-premises
     rev%coll%closed-iff-fixed-under-coll%closure)
    (apply-macete-with-minor-premises singleton-is-coll%closed)

    )))

(comment "Now we get serious.")

(def-theorem  le-is-coll%closed 
  "forall(a,b:points, not(a=b) implies coll%closed(le(a,b)))"
  (theory geometry-2)
  (proof
   (


   
    (unfold-single-defined-constant (0) coll%closed)
    direct-and-antecedent-inference-strategy
    (instantiate-theorem lines-are-le ("le(a,b)" "a_$0" "b_$0"))
    (block 
     (script-comment "node added by `instantiate-theorem' at (0 0 0 0)")
     (contrapose "with(f:sets[points],not(line(f)));")
     (apply-macete-with-minor-premises le-is-a-line))
    (instantiate-theorem collinear-implies-distinct ("a_$0" "b_$0" "x_$0"))
    (block 
     (script-comment "node added by `instantiate-theorem' at (0 1)")
     (backchain "with(f:sets[points],f=f);")
     (unfold-single-defined-constant (0) le)
     simplify
     (instantiate-theorem collinear-implies-distinct ("a_$0" "b_$0" "x_$0")))

    )))


(def-theorem le-equals-its-coll%closure
  "forall(a,b:points, not(a=b) implies coll%closure(le(a,b))=le(a,b))"
  (theory geometry-2)
  (proof
   (
    (apply-macete-with-minor-premises
     rev%coll%closed-iff-fixed-under-coll%closure)
    (apply-macete-with-minor-premises le-is-coll%closed)

    )))

(comment "Now two more general results about coll%closure which are true
 about closure under any relation. Unfortunately we need to prove the existence
 of coll%closure to prove these results. This approach may, however, be better
 in the full treatment."


(def-theorem monotonicity-of-coll%closure
  "forall(s,t:sets[points], s subseteq t implies
            coll%closure(s) subseteq coll%closure(t))"
  (theory geometry-2)
  (proof
   (
   

    )))

(def-theorem sandwich-lemma
  "forall(s,t:sets[points], s subseteq t  and t subseteq coll%closure(s)
                 implies
            coll%closure(s)=coll%closure(t))"
  (theory geometry-2)
  (proof
   (
   

    )))

)


(def-theorem  coll%closure-of-pair
  "forall(a,b:points, not(a = b) implies 
             coll%closure(indic{x:points, x=a or x=b})=le(a,b))"
  (theory geometry-2)
  (proof
   (

    (unfold-single-defined-constant (0) coll%closure)
    (apply-macete-with-minor-premises eliminate-iota-macete)
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises le-is-coll%closed)
    (block 
     (script-comment "node added by `direct-and-antecedent-inference-strategy' at (0 1)")
     (unfold-single-defined-constant (0) le)
     simplify-insistently)
    (block 
     (script-comment "node added by `direct-and-antecedent-inference-strategy' at (0 2 0
0 0)")
     (incorporate-antecedent "with(u_$1:sets[points],coll%closed(u_$1));")
     (apply-macete-with-minor-premises coll%closed-closed-under-le)
     direct-inference
     (incorporate-antecedent "with(u_$1:sets[points],b,a:points,
  indic{x_$1:points,  x_$1=a or x_$1=b} subseteq u_$1);")
     simplify-insistently)
    (block 
     (script-comment "node added by `direct-and-antecedent-inference-strategy' at (1 0 0
0 0)")
     (apply-macete-with-minor-premises tr%subseteq-antisymmetry)
     direct-inference
     simplify
     simplify)
    )))

(comment "Finally we show that two points determine a unique line. We already
 know that all three definitions of line are equivalent, and that any two
 points are on at least one line.")


(def-theorem two-points-determine-a-line
  "forall(s,t:sets[points],a,b:points, not a=b and line(s) and line(t) and
        a in s and b in s and a in t and b in t 
            implies
       s=t)"
  (theory geometry-2)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (instantiate-theorem lines-are-le ("s" "a" "b"))
    (instantiate-theorem lines-are-le ("t" "a" "b"))
 
  )))

(def-theorem intersection-of-two-lines
  "forall(s,t:sets[points],  
       line(s) and line(t) and not s=t 
         and
       nonempty_indic_q{s inters t} 
          implies 
        forsome(x:points, s inters t=singleton{x}))"
  
  (theory geometry-2)
  (proof
   (

    direct-and-antecedent-inference-strategy
    (instantiate-existential ("x_$0"))
    (contrapose "with(p:prop,not(p));")
    (apply-macete-with-minor-premises two-points-determine-a-line)
    (cut-with-single-formula "forsome(y:points, not y=x_$0 and y in s inters t)")
    (block 
     (script-comment "`cut-with-single-formula' at (0)")
     (antecedent-inference "with(p:prop,forsome(y:points,p));")
     auto-instantiate-existential
     (simplify-antecedent "with(p:prop,p and p);")
     (block 
      (script-comment "`auto-instantiate-existential' at (0 4)")
      (simplify-antecedent "with(x_$0:points,t,s:sets[points],x_$0 in s inters t);"))
     (simplify-antecedent "with(p:prop,p and p);")
     (simplify-antecedent "with(x_$0:points,t,s:sets[points],x_$0 in s inters t);"))
    (block 
     (script-comment "`cut-with-single-formula' at (1)")
     (contrapose "with(p:prop,not(p));")
     (apply-macete-with-minor-premises tr%subseteq-antisymmetry)
     direct-and-antecedent-inference-strategy
     (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (0)")
      simplify-insistently)
     (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (1)")
      simplify-insistently
      direct-and-antecedent-inference-strategy
      (simplify-antecedent "with(x_$0:points,f:sets[points],x_$0 in f);")
      (simplify-antecedent "with(x_$0:points,t,s:sets[points],x_$0 in s inters t);")))
    )))

(def-theorem le-equality-condition
  "forall(x,y,z:points, coll(x,y,z) implies le(x,y)=le(x,z))"
  (theory geometry-2)
  (proof
   (

    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "not x=y and not y=z and not x=z")
    (move-to-sibling 1)
    (block 
     (script-comment "`cut-with-single-formula' at (1)")
     (apply-macete-with-minor-premises collinear-implies-distinct))
    (block 
     (script-comment "`cut-with-single-formula' at (0)")
     (unfold-single-defined-constant-globally le)
     simplify
     (apply-macete-with-minor-premises tr%subseteq-antisymmetry)
     simplify-insistently
     direct-and-antecedent-inference-strategy
     (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (0 0 0 0 1)")
      (apply-macete-with-minor-premises collinear-flipper-2-3)
      simplify)
     (collinear-killer "y")
     simplify
     (collinear-killer "z"))
    )))

(def-theorem intersection-of-two-les
  "forall(a,b,c,d:points, not a=b and not c=d and 
      not  le(a,b)=le(c,d)
        and
       nonempty_indic_q{le(a,b) inters le(c,d)} 
      implies
        forsome(x:points, le(a,b) inters le(c,d)=singleton{x}))"
  
  (theory geometry-2)
  (proof
   (
   
   (apply-macete-with-minor-premises intersection-of-two-lines)
   (apply-macete-with-minor-premises le-is-a-line)
   )))


(def-theorem a-singleton-containing-a-particular-element
  "forall(s:sets[ind_1],a,b:ind_1,s=singleton{a} and b in s implies
             s=singleton{b})"
  (theory pure-generic-theory-1)
  (usages transportable-macete)  
  (proof
   (
    direct-and-antecedent-inference-strategy
    (incorporate-antecedent "with(b:ind_1,s:sets[ind_1],b in s);")
    (backchain-repeatedly ("with(a:ind_1,s:sets[ind_1],s=singleton{a});"))
    (weaken (0))
    simplify-insistently

    )))

(def-theorem intersection-of-les-with-common-first-point
  "forall(a,b,c:points, not a=b and not a=c and not b=c and
       not coll(a,b,c) implies le(b,a) inters le(b,c)=singleton{b})"
  (theory geometry-2)
  (proof
   (


    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "b in le(b,a) inters le(b,c)")
    (move-to-sibling 1)
    (block 
     (script-comment "`cut-with-single-formula' at (1)")
     (unfold-single-defined-constant-globally le)
     simplify)
    (cut-with-single-formula
     " forsome(x:points, le(b,a) inters le(b,c)=singleton{x})")
    (move-to-sibling 1)
    (apply-macete-with-minor-premises intersection-of-two-les)
    direct-and-antecedent-inference-strategy
    (contrapose "with(c,b,a:points,not(coll(a,b,c)));")
    (cut-with-single-formula "c in le(b,a)")
    (move-to-sibling 1)
    (block 
     (script-comment "`cut-with-single-formula' at (1)")
     (backchain "with(f:sets[points],f=f);")
     (unfold-single-defined-constant (0) le)
     simplify)
    (block 
     (script-comment "`cut-with-single-formula' at (0)")
     (incorporate-antecedent "with(c,a,b:points,c in le(b,a));")
     (unfold-single-defined-constant (0) le)
     simplify
     direct-and-antecedent-inference-strategy
     (apply-macete-with-minor-premises coll-disjunctive-permuter)
     simplify)
    (instantiate-existential ("b"))
    (block 
     (script-comment "`cut-with-single-formula' at (0)")
     (apply-macete-with-minor-premises tr%a-singleton-containing-a-particular-element)
     simplify)

    )))

(comment "Here are some simple lemmas that are useful in working with Pasch
  and which may make good exercises in themselves.")

(def-theorem non-collinear-between
  "forall(x,y,z,p:points,not x=y and not x=z and not y=z and not coll(x,y,z) and
    bet(x,p,y) implies not coll(p,y,z))"
  (theory geometry-2)
  (proof
   (

    direct-and-antecedent-inference-strategy
    (contrapose "with(z,y,x:points,not(coll(x,y,z)));")
    (collinear-killer "p")
    )))

(def-theorem non-collinear-right
  "forall(x,y,z,p:points,not x=y and not x=z and not y=z and
    not coll(x,y,z) and
    bet(x,y,p) implies not coll(p,y,z))"
  (theory geometry-2)
  (proof
   (

    direct-and-antecedent-inference-strategy
    (contrapose "with(z,y,x:points,not(coll(x,y,z)));")
    (collinear-killer "p")
   
    )))

(def-theorem non-collinear-left
   "forall(x,y,z,p:points,not x=y and not x=z and not y=z and
    not coll(x,y,z) and
    bet(y,x,p) implies not coll(p,y,z))"
   (theory geometry-2)
   (proof
    (

      direct-and-antecedent-inference-strategy
     (contrapose "with(z,y,x:points,not(coll(x,y,z)));")
     (collinear-killer "p")
   
     )))

(def-theorem non-collinear
  "forall(x,y,z,p:points,not x=y and not x=z and not y=z and
    not coll(x,y,z) and
    coll(x,y,p) implies not coll(p,y,z))"
  (theory geometry-2)
  (proof
   (

   
    direct-and-antecedent-inference-strategy
    (contrapose "with(p,y,x:points,coll(x,y,p));")
    unfold-defined-constants
    (contrapose "with(z,y,p:points,coll(p,y,z));")
    (antecedent-inference "with(p:prop,p or p or p);")
    (block 
     (script-comment "`antecedent-inference' at (0)")
     (apply-macete-with-minor-premises non-collinear-right)
     auto-instantiate-existential)
    (block 
     (script-comment "`antecedent-inference' at (1)")
     (apply-macete-with-minor-premises non-collinear-left)
     auto-instantiate-existential)
    (block 
     (script-comment "`antecedent-inference' at (2)")
     (apply-macete-with-minor-premises non-collinear-between)
     auto-instantiate-existential)
    )))

(def-theorem non-equality-1
  "forall(x,y,z,p:points,not x=y and not x=z and not y=z and
    not coll(x,y,z) and
    coll(x,y,p) implies not p=z)"
  (theory geometry-2)
  (proof
   (

    direct-and-antecedent-inference-strategy
    (contrapose "with(z,y,x:points,not(coll(x,y,z)));")
    (backchain-backwards "with(z,p:points,p=z);")
   
    )))

(def-theorem inequality-2
  "forall(x,y,z,p,q:points,not x=y and not x=z and not y=z and
    not coll(x,y,z) and
    coll(x,y,p) and coll(x,z,q) implies not p=q)"
  (theory geometry-2)
  (proof
   (

    direct-and-antecedent-inference-strategy
    (contrapose "with(z,y,x:points,not(coll(x,y,z)));")
    (incorporate-antecedent "with(q,z,x:points,coll(x,z,q));")
    (backchain-backwards "with(q,p:points,p=q);")
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises switching-all-cases)
    (instantiate-existential ("p"))
    (block 
     (script-comment "`instantiate-existential' at (0 0 1)")
     (apply-macete-with-minor-premises collinear-flipper-1-3)
     (move-to-ancestor 1)
     (apply-macete-with-minor-premises coll-disjunctive-permuter)
     simplify)
    (block 
     (script-comment "`instantiate-existential' at (0 0 2)")
     (apply-macete-with-minor-premises switching-all-cases)
     (instantiate-existential ("x"))
     (block 
      (script-comment "`instantiate-existential' at (0 0 0)")
      (apply-macete-with-minor-premises collinear-implies-distinct-lemma)
      auto-instantiate-existential)
     (collinear-killer "p"))

    )))


(def-theorem non-collinear-2
  "forall(x,y,z,p,q:points,not x=y and not x=z and not y=z and
    not coll(x,y,z) and
    coll(x,y,p) and coll(x,z,q) implies not coll(p,q,x))"
  (theory geometry-2)
  (proof
   (

  
   
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "not p=q and not q=y and not p=z")
    (move-to-sibling 1)
    (block 
     (script-comment "`cut-with-single-formula' at (1)")
     direct-and-antecedent-inference-strategy
     (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (0)")
      (apply-macete-with-minor-premises inequality-2)
      auto-instantiate-existential)
     (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (1)")
      (apply-macete-with-minor-premises non-equality-1)
      (instantiate-existential ("z" "x"))
      simplify
      (block 
       (script-comment "`instantiate-existential' at (0 3)")
       (contrapose "with(z,y,x:points,not(coll(x,y,z)));")
       (apply-macete-with-minor-premises collinear-flipper-2-3)))
     (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (2)")
      (apply-macete-with-minor-premises non-equality-1)
      (instantiate-existential ("y" "x"))))
    (block 
     (script-comment "`cut-with-single-formula' at (0)")
     (contrapose "with(z,y,x:points,not(coll(x,y,z)));")
     (cut-with-single-formula "coll(p,q,y) and coll(p,q,z)")
     (block 
      (script-comment "`cut-with-single-formula' at (0)")
      (apply-macete-with-minor-premises triple-switching)
      auto-instantiate-existential)
     (block 
      (script-comment "`cut-with-single-formula' at (1)")
      direct-and-antecedent-inference-strategy
      (collinear-killer "x")
      (collinear-killer "x")))
    )))


(def-theorem non-collinear-2-other
  "forall(x,y,z,p,q:points,not x=y and not x=z and not y=z and
    not coll(x,y,z) and
    coll(x,y,p) and coll(x,z,q) implies not coll(p,q,y))"
  (theory geometry-2)
  (proof
   (

  

    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "not coll(q,x,y)")
    (move-to-sibling 1)
    (block 
     (script-comment "`cut-with-single-formula' at (1)")
     (apply-macete-with-minor-premises non-collinear)
     (instantiate-existential ("z"))
     simplify
     simplify
     (block 
      (script-comment "`instantiate-existential' at (0 3)")
      (apply-macete-with-minor-premises coll-conjunctive-permuter)
      simplify)
     (apply-macete-with-minor-premises collinear-flipper-1-2))
    (block 
     (script-comment "`cut-with-single-formula' at (0)")
     (apply-macete-with-minor-premises collinear-flipper-2-3)
     (apply-macete-with-minor-premises non-collinear)
     (instantiate-existential ("x"))
     (block 
      (script-comment "`instantiate-existential' at (0 1)")
      (apply-macete-with-minor-premises collinear-implies-distinct-lemma)
      (apply-macete-with-minor-premises collinear-flipper-2-3)
      auto-instantiate-existential)
     (block 
      (script-comment "`instantiate-existential' at (0 2)")
      (force-substitution "y=q" "q=y" (0))
      (block 
       (script-comment "`force-substitution' at (0)")
       (apply-macete-with-minor-premises non-equality-1)
       (instantiate-existential ("y" "x"))
       (move-to-ancestor 2)
       (instantiate-existential ("z" "x"))
       (apply-macete-with-minor-premises collinear-flipper-2-3))
      simplify)
     (block 
      (script-comment "`instantiate-existential' at (0 3)")
      (apply-macete-with-minor-premises coll-conjunctive-permuter)
      simplify))
   
  
    )))




(def-theory geometry-3
   (component-theories geometry-2 h-o-real-arithmetic)
    )

(include-files (files (imps theories/geometry/closure)))

(def-translation Rel-to-coll
  (source three-place-predicate-theory)
  (target geometry-3)
   (sort-pairs (ind_1 points))
  (constant-pairs (Rel coll))
  (fixed-theories h-o-real-arithmetic)   
  (theory-interpretation-check using-simplification))

(def-theorem coll%closure-exists
  "forall(s:sets[points],#(coll%closure(s)))"
  (theory geometry-3)
  (proof
   (
   

    (apply-macete-with-minor-premises tr%rel%closure-exists)
    )))


(comment "Before proceeding to the next axiom, we introduce some informal
  terminology, that is, terminology we will use in our comments, but not
  in the official IMPS specifications. Given bet(a,b,c), we will say that a
 lies on the opposite side of b from c, or that b separates a and c. The next
 axioms say that if b separates a and c and d is on the same line then either
 d is on the opposite side of b from a, or from c, but on only one of these 
  sides.")


(def-theory geometry-4
  (component-theories geometry-3)
  (axioms
    
   

    (a-point-separates-a-line-or
     "forall(a,b,m,p:points, bet(a,m,b) and coll(a,b,p) and not p=m
             implies 
            (bet(a,m,p) or bet(p,m,b)))")

    (a-point-separates-a-line-not-both "forall(a,b,m,p:points, bet(a,m,b) and
           coll(a,b,p) and bet(a,m,p) implies not( bet(p,m,b)))")
    
   )
   )
(comment "look the follwoing proof over in view of the proof of extending")

(def-theorem nesting
  "forall(a,b,c,d:points, bet(a,b,d) and bet(b,c,d) implies bet(a,c,d))"
  (theory geometry-4)
  (proof
   (


    
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "not a=c")
    (move-to-sibling 1)
    (block 
     (script-comment "`cut-with-single-formula' at (1)")
     (contrapose "with(d,c,b:points,bet(b,c,d));")
     (backchain-backwards "with(c,a:points,a=c);")
     (apply-macete-with-minor-premises anti-cyclic))
    (block 
     (script-comment "`cut-with-single-formula' at (0)")
     (cut-with-single-formula "(bet(b,c,a) or bet(a,c,d))")
     (move-to-sibling 1)
     (block 
      (script-comment "`cut-with-single-formula' at (1)")
      (apply-macete-with-minor-premises a-point-separates-a-line-or)
      (apply-macete-with-minor-premises collinear-all-cases)
      simplify)
     (block 
      (script-comment "`cut-with-single-formula' at (0)")
      (cut-with-single-formula "bet(a,b,c) or bet(c,b,d)")
      (move-to-sibling 1)
      (block 
       (script-comment "`cut-with-single-formula' at (1)")
       (apply-macete-with-minor-premises a-point-separates-a-line-or)
       direct-and-antecedent-inference-strategy
       (block 
	(script-comment "`direct-and-antecedent-inference-strategy' at (1)")
	(apply-macete-with-minor-premises collinear-flipper-2-3)
	(apply-macete-with-minor-premises switching)
	(instantiate-existential ("b"))
	(block 
	 (script-comment "`instantiate-existential' at (0 1)")
	 (apply-macete-with-minor-premises collinear-all-cases)
	 simplify)
	(block 
	 (script-comment "`instantiate-existential' at (0 2)")
	 (apply-macete-with-minor-premises collinear-all-cases)
	 simplify))
       (block 
	(script-comment "`direct-and-antecedent-inference-strategy' at (2)")
	(force-substitution "c=b" "b=c" (0))
	(move-to-sibling 1)
	simplify
	(block 
	 (script-comment "`force-substitution' at (0)")
	 (apply-macete-with-minor-premises distinctness-1-2)
	 auto-instantiate-existential)))
      (block 
       (script-comment "`cut-with-single-formula' at (0)")
       (antecedent-inference-strategy (0 1))
       (block 
	(script-comment "`antecedent-inference-strategy' at (0 0)")
	(contrapose "with(c,b,a:points,bet(a,b,c));")
	(apply-macete-with-minor-premises symmetry-of-betweeness)
	(apply-macete-with-minor-premises anti-cyclic))
       (block 
	(script-comment "`antecedent-inference-strategy' at (1 0)")
	(contrapose "with(d,b,c:points,bet(c,b,d));")
	(apply-macete-with-minor-premises anti-cyclic)))))

    )))

(def-theorem other-nesting 
  "forall(a,b,c,d:points, bet(d,b,a) and bet(d,a,c) implies bet(d,b,c))"
  (theory geometry-4)
  (proof
   (


    (apply-macete-with-minor-premises symmetry-of-betweeness)
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises nesting)
    auto-instantiate-existential
    )))

(def-theorem nesting-2 
  "forall(a,b,c,d:points,  not b=d and bet(a,b,c) and bet(a,c,d) implies bet(b,c,d))"
  (theory geometry-4)
  (proof
   (



    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "bet(d,c,b) or bet(b,c,a)")
    (move-to-sibling 1)
    (block 
     (script-comment "`cut-with-single-formula' at (1)")
     (apply-macete-with-minor-premises a-point-separates-a-line-or)
     direct-and-antecedent-inference-strategy
     (apply-macete-with-minor-premises symmetry-of-betweeness)
     (collinear-killer "c")
     (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (2)")
      (apply-macete-with-minor-premises distinctness-2-3)
      auto-instantiate-existential))
    (block 
     (script-comment "`cut-with-single-formula' at (0)")
     (antecedent-inference "with(p:prop,p or p);")
     (apply-macete-with-minor-premises symmetry-of-betweeness)
     (block 
      (script-comment "`antecedent-inference' at (1)")
      (contrapose "with(a,c,b:points,bet(b,c,a));")
      (apply-macete-with-minor-premises anti-cyclic)
      (apply-macete-with-minor-premises symmetry-of-betweeness)))
   
    )))

(def-theorem extending 
  "forall(a,b,c,d:points,  not a=d and bet(a,b,c) and
          bet(b,c,d) implies bet(a,c,d))"
  (theory geometry-4)
  (proof
   (

direct-and-antecedent-inference-strategy
(cut-with-single-formula "not a=c")
(move-to-sibling 1)
(block 
  (script-comment "`cut-with-single-formula' at (1)")
       (apply-macete-with-minor-premises distinctness-1-3)
       auto-instantiate-existential)
(block 
  (script-comment "`cut-with-single-formula' at (0)")
       (cut-with-single-formula "bet(b,c,a) or bet(a,c,d)")
       (move-to-sibling 1)
       (block 
  (script-comment "`cut-with-single-formula' at (1)")
              (apply-macete-with-minor-premises a-point-separates-a-line-or)
              simplify
              (collinear-killer "c"))
       (block 
  (script-comment "`cut-with-single-formula' at (0)")
              (antecedent-inference "with(p:prop,p or p);")
              (contrapose "with(a,c,b:points,bet(b,c,a));")
              (apply-macete-with-minor-premises anti-cyclic)
              (apply-macete-with-minor-premises symmetry-of-betweeness)))
  
    )))

(def-theorem other-extending 
  "forall(a,b,c,d:points,  not a=d and bet(a,b,c) and
          bet(b,c,d) implies bet(a,b,d))"
  (theory geometry-4)
  (proof
   (

  
    (apply-macete-with-minor-premises symmetry-of-betweeness)
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises extending)
    auto-instantiate-existential
    simplify
    )))



(include-files (files (imps theories/cardinality/cardinality-supplements)))

(def-theorem f_card_difference
  f_card_difference
  (theory generic-theory-1)
  (usages transportable-macete)
  (proof existing-theorem))


(def-theorem empty-segment-lemma
  "forall(p:points, s:sets[points], f_indic_q{s} and nonempty_indic_q{s}
               implies 
           forsome(x:points, x in s and 
                 forall(y:points, y in s implies not(bet(p,y,x)))))"
  (theory geometry-4)
  (proof
   (


    (apply-macete-with-minor-premises tr%iota-free-definition-of-f-indic-q)
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "1<=n")
    (move-to-sibling 1)
    (block 
     (script-comment "`cut-with-single-formula' at (1)")
     (backchain-backwards "with(n:nn,n=n);")
     (cut-with-single-formula "0<=f_card{s} and not(f_card{s}=0)")
     simplify
     (block 
      (script-comment "`cut-with-single-formula' at (1)")
      (apply-macete-with-minor-premises tr%empty-indic-has-f-card-zero)
      simplify
      (contrapose "with(x:points,s:sets[points],x in s);")
      (backchain "with(f,s:sets[points],s=f);")
      (weaken (0 1))
      simplify))
    (block 
     (script-comment "`cut-with-single-formula' at (0)")
     (cut-with-single-formula "forall(n:zz, 1<=n implies forall(s:sets[points],
              f_card{s}=n  implies forsome(x:points,
                 x in s
         and 
    forall(y:points,y in s implies not(bet(p,y,x))))))")
     simplify
     (block 
      (script-comment "`cut-with-single-formula' at (1)")
      (weaken (0 1 2))
      (induction trivial-integer-inductor ("n"))
      (block 
       (script-comment "`induction' at (0 0)")
       beta-reduce-repeatedly
       (apply-macete-with-minor-premises tr%singleton-has-f-card-one)
       direct-and-antecedent-inference-strategy
       (instantiate-existential ("y"))
       (block 
	(script-comment "`instantiate-existential' at (0 0)")
	(backchain "with(p:prop,p);")
	(apply-macete-with-minor-premises tr%singleton-equality-conversion))
       (block 
	(script-comment "`instantiate-existential' at (0 1 0 0)")
	(cut-with-single-formula "y=y_$0")
	(move-to-sibling 1)
	(block 
	 (script-comment "`cut-with-single-formula' at (1)")
	 (contrapose "with(y_$0:points,s:sets[points],y_$0 in s);")
	 (backchain "with(f,s:sets[points],s=f);")
	 (apply-macete-with-minor-premises tr%singleton-equality-conversion)
	 simplify)
	(block 
	 (script-comment "`cut-with-single-formula' at (0)")
	 (contrapose "with(y_$0,y:points,y=y_$0);")
	 (force-substitution "y=y_$0" "y_$0=y" (0))
	 (move-to-sibling 1)
	 simplify
	 (block 
	  (script-comment "`force-substitution' at (0)")
	  (apply-macete-with-minor-premises distinctness-2-3)
	  auto-instantiate-existential))))
      (block 
       (script-comment "`induction' at (0 1 0 0 0 0 0 0)")
       (cut-with-single-formula "forsome(x:points, x in s)")
       (move-to-sibling 1)
       (block 
	(script-comment "`cut-with-single-formula' at (1)")
	(apply-macete-with-minor-premises tr%rev%positive-f-card-iff-nonempty)
	simplify)
       (block 
	(script-comment "`cut-with-single-formula' at (0)")
	(antecedent-inference "with(s:sets[points],nonempty_indic_q{s});")
	(instantiate-universal-antecedent "with(p:prop,forall(s:sets[points],p));"
					  ("s diff singleton{x}"))
	(block 
	 (script-comment "`instantiate-universal-antecedent' at (0 0 0)")
	 (contrapose "with(p:prop,not(p));")
	 (apply-macete-with-minor-premises tr%f_card_difference)
	 (move-to-sibling 1)
	 simplify-insistently
	 (block 
	  (script-comment "`apply-macete-with-minor-premises' at (0)")
	  (apply-macete-with-minor-premises tr%singleton-has-f-card-one-rewrite)
	  simplify))
	(block 
	 (script-comment "`instantiate-universal-antecedent' at (0 0 1 0 0)")
	 (incorporate-antecedent "with(p:prop,forall(y_$1:points,p));")
	 (apply-macete-with-minor-premises indicator-facts-macete)
	 simplify
	 direct-and-antecedent-inference-strategy
	 (incorporate-antecedent "with(x_$4:points,f,s:sets[points],x_$4 in s diff f);")
	 (apply-macete-with-minor-premises indicator-facts-macete)
	 simplify
	 direct-and-antecedent-inference-strategy
	 (case-split ("bet(p,x,x_$4)"))
	 (move-to-sibling 2)
	 (block 
	  (script-comment "`case-split' at (2)")
	  (instantiate-existential ("x_$4"))
	  simplify
	  (case-split ("y=x"))
	  simplify
	  simplify)
	 (block 
	  (script-comment "`case-split' at (1)")
	  (instantiate-existential ("x"))
	  (case-split ("y=x"))
	  (block 
	   (script-comment "`case-split' at (1)")
	   (contrapose "with(x,y:points,y=x);")
	   (apply-macete-with-minor-premises distinctness-2-3)
	   auto-instantiate-existential)
	  (block 
	   (script-comment "`case-split' at (2)")
	   (contrapose "with(p:prop,forall(y_$1:points,p));")
	   (instantiate-existential ("y"))
	   (apply-macete-with-minor-premises other-nesting)
	   auto-instantiate-existential)))))))

    )))



(def-theory geometry-5
  (component-theories geometry-4)
  (axioms
    (weak-pasch
     "forall(a,b,c,d,e:points, 
            not coll(a,b,c) and 
            not a=b and 
            bet(b,c,d) and 
            bet(a,e,c)
            implies
           forsome(f:points, f in le(d,e) and  bet(a,f,b)))")))
 


(def-theorem weak-pasch-ordered-lemma
  "forall(d,c,e,b,f,a:points,
     bet(a,f,b)
      and 
     bet(a,e,c)
      and 
     bet(b,c,d)
      and 
     not(coll(a,b,c))
      implies 
     not(bet(d,f,e)))"
  (theory geometry-5)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "not a=c and not b=c and not b=d and not c=d and not b=f and not f=a and not b=a and not a=f and not e=c")
    (move-to-sibling 1)
    inequality-killer
    (cut-with-single-formula "not coll(d,e,c)")
    (move-to-sibling 1)
    (block 
     (script-comment "`cut-with-single-formula' at (1)")
     (apply-macete-with-minor-premises non-collinear-2)
     (instantiate-existential ("a" "b"))
     simplify
     simplify
     (block 
      (script-comment "`instantiate-existential' at (0 3)")
      (contrapose "with(c,b,a:points,not(coll(a,b,c)));")
      (apply-macete-with-minor-premises collinear-flipper-1-3))
     (block 
      (script-comment "`instantiate-existential' at (0 4)")
      (apply-macete-with-minor-premises collinear-all-cases)
      simplify)
     (block 
      (script-comment "`instantiate-existential' at (0 5)")
      (apply-macete-with-minor-premises collinear-all-cases)
      simplify))
    (contrapose "with(c,b,a:points,not(coll(a,b,c)));")
    (cut-with-single-formula "forsome(x:points, x in le(a,f) and bet(d,x,c))")
    (move-to-sibling 1)
    (block 
     (script-comment "`cut-with-single-formula' at (1)")
     (apply-macete-with-minor-premises weak-pasch)
     auto-instantiate-existential
     (block 
      (script-comment "`auto-instantiate-existential' at (0 0)")
      (contrapose "with(c,e,d:points,not(coll(d,e,c)));")
      (apply-macete-with-minor-premises collinear-flipper-2-3))
     simplify
     (apply-macete-with-minor-premises symmetry-of-betweeness))
    (antecedent-inference "with(p:prop,forsome(x:points,p));")
    (cut-with-single-formula "x in le(b,c) inters le(b,a)")
    (move-to-sibling 1)
    (block 
     (script-comment "`cut-with-single-formula' at (1)")
     (unfold-single-defined-constant-globally le)
     simplify
     direct-and-antecedent-inference-strategy
     (collinear-killer "d")
     (move-to-sibling 2)
     (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (1 0 2)")
      (cut-with-single-formula "le(a,b)=le(a,f)")
      (move-to-sibling 1)
      (block 
       (script-comment "`cut-with-single-formula' at (1)")
       (apply-macete-with-minor-premises le-equality-condition)
       (apply-macete-with-minor-premises collinear-all-cases)
       simplify)
      (block 
       (script-comment "`cut-with-single-formula' at (0)")
       (antecedent-inference "with(p:prop,p and p);")
       (incorporate-antecedent "with(x:points,f:sets[points],x in f);")
       (backchain-backwards "with(f:sets[points],f=f);")
       (unfold-single-defined-constant (0) le)
       simplify
       (apply-macete-with-minor-premises collinear-all-cases)
       direct-and-antecedent-inference-strategy))
     (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (1 0 1)")
      (contrapose "with(c,x:points,x=c);")
      (apply-macete-with-minor-premises distinctness-2-3)
      auto-instantiate-existential))
    (block 
     (script-comment "`cut-with-single-formula' at (0)")
     (contrapose "with(c,e,d:points,not(coll(d,e,c)));")
     (cut-with-single-formula "le(b,c) inters le(b,a)=singleton{b}")
     (move-to-sibling 1)
     (block 
      (script-comment "`cut-with-single-formula' at (1)")
      (apply-macete-with-minor-premises intersection-of-les-with-common-first-point)
      (apply-macete-with-minor-premises collinear-flipper-1-3))
     (block 
      (script-comment "`cut-with-single-formula' at (0)")
     (incorporate-antecedent "with(x:points,f:sets[points],x in f);")
      (backchain "with(f:sets[points],f=f);")
      simplify-insistently
      direct-and-antecedent-inference-strategy
      (antecedent-inference "with(p:prop,p and p);")
      (contrapose "with(c,x,d:points,bet(d,x,c));")
      (backchain "with(b,x:points,x=b);")
      (apply-macete-with-minor-premises symmetry-of-betweeness)
      (apply-macete-with-minor-premises anti-cyclic))))))

  
(def-theorem weak-pasch-ordered
  "forall(a,b,c,d,e,f:points, 
            not coll(a,b,c) and 
            bet(b,c,d) and 
            bet(a,e,c) and 
            f in le(d,e) and  
            bet(a,f,b)
              implies
           bet(d,e,f))"
  (theory geometry-5)
  (proof
   (


    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "not a=c and not b=c and not b=d and not c=d and not b=f and not f=a and not b=a and not a=f and not a=e")
    (move-to-sibling 1)
    inequality-killer
    (block 
     (script-comment "`cut-with-single-formula' at (0)")
     (incorporate-antecedent "with(f:points,f) in with(f:sets[points],f);")
     (unfold-single-defined-constant-globally le)
     simplify
     direct-and-antecedent-inference-strategy
     (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (0 0 0)")
      (contrapose "with(d,f:points,f=d);")
      (weaken (0))
      (cut-with-single-formula " le(b,a) inters le(b,c)=singleton{b}")
      (move-to-sibling 1)
      (apply-macete-with-minor-premises intersection-of-les-with-common-first-point)
      (block 
       (script-comment "`cut-with-single-formula' at (0)")
       (incorporate-antecedent "with(f:sets[points],f=f);")
       (apply-macete-with-minor-premises tr%subseteq-antisymmetry)
       direct-and-antecedent-inference-strategy
       (incorporate-antecedent "with(b:points,f:sets[points],
  f inters f subseteq singleton{b});")
       unfold-defined-constants
       simplify-insistently
       direct-and-antecedent-inference-strategy
       (instantiate-universal-antecedent "with(b:points,p:prop,
  forall(x_$2:points,p and p implies x_$2=b));"
					 ("d"))
       (block 
	(script-comment "`instantiate-universal-antecedent' at (0 0 0 0 0)")
	(contrapose "with(d,a,b:points,not(coll(b,a,d)));")
	(apply-macete-with-minor-premises collinear-all-cases)
	simplify)
       (block 
	(script-comment "`instantiate-universal-antecedent' at (0 0 0 1 0)")
	(contrapose "with(d,c,b:points,not(coll(b,c,d)));")
	(apply-macete-with-minor-premises collinear-all-cases)
	simplify)))
     (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (0 0 1)")
      (contrapose "with(e,f:points,f=e);")
      (weaken (0))
      (cut-with-single-formula " le(a,b) inters le(a,c)=singleton{a}")
      (move-to-sibling 1)
      (block 
       (script-comment "`cut-with-single-formula' at (1)")
       (apply-macete-with-minor-premises intersection-of-les-with-common-first-point)
       (contrapose "with(c,b,a:points,not(coll(a,b,c)));")
       (apply-macete-with-minor-premises collinear-flipper-1-2))
      (block 
       (script-comment "`cut-with-single-formula' at (0)")
       (incorporate-antecedent "with(f:sets[points],f=f);")
       (apply-macete-with-minor-premises tr%subseteq-antisymmetry)
       direct-and-antecedent-inference-strategy
       (incorporate-antecedent "with(a:points,f:sets[points],
  f inters f subseteq singleton{a});")
       unfold-defined-constants
       simplify-insistently
       direct-and-antecedent-inference-strategy
       (auto-instantiate-universal-antecedent "with(c,b,a:points,
  forall(x_$2:points,
    (x_$2=a or x_$2=b or coll(a,b,x_$2))
     and 
    (x_$2=a or x_$2=c or coll(a,c,x_$2))
     implies 
    x_$2=a));")
       (block 
	(script-comment "`auto-instantiate-universal-antecedent' at (0 0 0 0 0)")
	(contrapose "with(f,b,a:points,not(coll(a,b,f)));")
	(apply-macete-with-minor-premises collinear-all-cases)
	simplify)
       (block 
	(script-comment "`auto-instantiate-universal-antecedent' at (0 0 0 1 0)")
	(contrapose "with(f,c,a:points,not(coll(a,c,f)));")
	(apply-macete-with-minor-premises collinear-all-cases)
	simplify)))
     (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (0 0 2)")
      (incorporate-antecedent "with(f,e,d:points,coll(d,e,f));")
      (unfold-single-defined-constant (0) coll)
      direct-and-antecedent-inference-strategy
      (move-to-sibling 2)
      (block 
       (script-comment "`direct-and-antecedent-inference-strategy' at (0 2)")
       (contrapose "with(e,f,d:points,bet(d,f,e));")
       (apply-macete-with-minor-premises weak-pasch-ordered-lemma)
       auto-instantiate-existential)
      (block 
       (script-comment "`direct-and-antecedent-inference-strategy' at (0 1)")
       (cut-with-single-formula "not coll(f,e,a)")
       (move-to-sibling 1)
       (block 
	(script-comment "`cut-with-single-formula' at (1)")
	(apply-macete-with-minor-premises non-collinear-2)
	(instantiate-existential ("c" "b"))
	(block 
	 (script-comment "`instantiate-existential' at (0 4)")
	 (apply-macete-with-minor-premises collinear-all-cases)
	 simplify)
	(block 
	 (script-comment "`instantiate-existential' at (0 5)")
	 (apply-macete-with-minor-premises collinear-all-cases)
	 simplify))
       (block 
	(script-comment "`cut-with-single-formula' at (0)")
	(cut-with-single-formula "forsome(x:points, x in le(b,d) and  bet(e,x,a))")
	(move-to-sibling 1)
	(block 
	 (script-comment "`cut-with-single-formula' at (1)")
	 (apply-macete-with-minor-premises weak-pasch)
	 (instantiate-existential ("f"))
	 (block 
	  (script-comment "`instantiate-existential' at (0 0)")
	  (contrapose "with(a,e,f:points,not(coll(f,e,a)));")
	  (apply-macete-with-minor-premises coll-disjunctive-permuter)
	  simplify)
	 simplify)
	(block 
	 (script-comment "`cut-with-single-formula' at (0)")
	 (antecedent-inference "with(p:prop,forsome(x:points,p));")
	 (cut-with-single-formula "x in le(c,a) inters le(c,b)")
	 (move-to-sibling 1)
	 (block 
	  (script-comment "`cut-with-single-formula' at (1)")
	  (unfold-single-defined-constant-globally le)
	  simplify
	  direct-and-antecedent-inference-strategy
	  (collinear-killer "e")
	  (move-to-sibling 2)
	  (block 
	   (script-comment "`direct-and-antecedent-inference-strategy' at (1 0 2)")
	   (cut-with-single-formula "le(b,c)=le(b,d)")
	   (move-to-sibling 1)
	   (block 
	    (script-comment "`cut-with-single-formula' at (1)")
	    (apply-macete-with-minor-premises le-equality-condition)
	    (apply-macete-with-minor-premises collinear-all-cases)
	    simplify)
	   (block 
	    (script-comment "`cut-with-single-formula' at (0)")
	    (antecedent-inference "with(p:prop,p and p);")
	    (incorporate-antecedent "with(x:points,f:sets[points],x in f);")
	    (backchain-backwards "with(f:sets[points],f=f);")
	    (unfold-single-defined-constant (0)
                                                                 
					    le)
	    simplify
	    (apply-macete-with-minor-premises collinear-all-cases)
	    direct-and-antecedent-inference-strategy))
	  (block 
	   (script-comment "`direct-and-antecedent-inference-strategy' at (1 0 1)")
	   (contrapose "with(a,x:points,x=a);")
	   (apply-macete-with-minor-premises distinctness-2-3)
	   auto-instantiate-existential))
	 (block 
	  (script-comment "`cut-with-single-formula' at (0)")
	  (contrapose "with(a,e,f:points,not(coll(f,e,a)));")
	  (cut-with-single-formula "le(c,a) inters le(c,b)=singleton{c}")
	  (move-to-sibling 1)
	  (block 
	   (script-comment "`cut-with-single-formula' at (1)")
	   (apply-macete-with-minor-premises intersection-of-les-with-common-first-point)
	   (apply-macete-with-minor-premises collinear-flipper-2-3))
	  (block 
	   (script-comment "`cut-with-single-formula' at (0)")
	   (incorporate-antecedent "with(x:points,f:sets[points],x in f);")
	   (backchain "with(f:sets[points],f=f);")
	   simplify-insistently
	   direct-and-antecedent-inference-strategy
	   (antecedent-inference "with(p:prop,p and p);")
	   (contrapose "with(a,x,e:points,bet(e,x,a));")
	   (backchain "with(c,x:points,x=c);")
	   (apply-macete-with-minor-premises anti-cyclic)
	   (apply-macete-with-minor-premises symmetry-of-betweeness))))))))
    )))

(def-theorem weak-pasch-other 
  "forall(a,b,c,d,f:points,  
       not coll(a,b,c) and 
       not a=c and 
       bet(b,c,d) and 
       bet(a,f,b)
         implies
       forsome(e:points, coll(d,e,f) and bet(a,e,c)))"
  (theory geometry-5)
  (proof
   (

  
  
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "not b=c and not b=d and not c=d and not b=f and not f=a and not b=a and not a=f")
    (move-to-sibling 1)
    inequality-killer
    (cut-with-single-formula "not d=f")
    (move-to-sibling 1)
    (block 
     (script-comment "`cut-with-single-formula' at (1)")
     (apply-macete-with-minor-premises inequality-2)
     (instantiate-existential ("a" "c" "b"))
     simplify
     (block 
      (script-comment "`instantiate-existential' at (0 3)")
      (apply-macete-with-minor-premises coll-conjunctive-permuter)
      (prove-by-logic-and-simplification 3))
     (block 
      (script-comment "`instantiate-existential' at (0 4)")
      (apply-macete-with-minor-premises collinear-all-cases)
      simplify)
     (block 
      (script-comment "`instantiate-existential' at (0 5)")
      (apply-macete-with-minor-premises collinear-all-cases)
      simplify))
    (cut-with-single-formula "not d=a")
    (move-to-sibling 1)
    (block 
     (script-comment "`cut-with-single-formula' at (1)")
     (apply-macete-with-minor-premises non-equality-1)
     (instantiate-existential ("b" "c"))
     simplify
     (block 
      (script-comment "`instantiate-existential' at (0 3)")
      (apply-macete-with-minor-premises coll-conjunctive-permuter)
      simplify)
     (block 
      (script-comment "`instantiate-existential' at (0 4)")
      (apply-macete-with-minor-premises coll-disjunctive-permuter)
      simplify))
    (cut-with-single-formula "not coll(d,c,a)")
    (move-to-sibling 1)
    (block 
     (script-comment "`cut-with-single-formula' at (1)")
     (apply-macete-with-minor-premises non-collinear)
     auto-instantiate-existential)
    (cut-with-single-formula "forsome(h:points,bet(h,b,f))")
    (move-to-sibling 1)
    (apply-macete-with-minor-premises existence-left)
    (antecedent-inference "with(p:prop,forsome(h:points,p));")
    (cut-with-single-formula "not coll(f,d,b)")
    (move-to-sibling 1)
    (block 
     (script-comment "`cut-with-single-formula' at (1)")
     (apply-macete-with-minor-premises non-collinear-2)
     (instantiate-existential ("c" "a"))
     (apply-macete-with-minor-premises collinear-flipper-1-2))
    (cut-with-single-formula " forsome(r:points, r in le(h,c) and  bet(d,r,f))")
    (move-to-sibling 1)
    (block 
     (script-comment "`cut-with-single-formula' at (1)")
     (apply-macete-with-minor-premises weak-pasch)
     (instantiate-existential ("b"))
     (apply-macete-with-minor-premises collinear-flipper-1-2)
     (apply-macete-with-minor-premises symmetry-of-betweeness)
     (apply-macete-with-minor-premises symmetry-of-betweeness))
    (antecedent-inference "with(p:prop,forsome(r:points,p));")
    (cut-with-single-formula "bet(h,c,r)")
    (move-to-sibling 1)
    (block 
     (script-comment "`cut-with-single-formula' at (1)")
     (apply-macete-with-minor-premises weak-pasch-ordered)
     (instantiate-existential ("b" "f" "d")))
    (cut-with-single-formula "bet(a,f,h)")
    (move-to-sibling 1)
    (block 
     (script-comment "`cut-with-single-formula' at (1)")
     (apply-macete-with-minor-premises other-extending)
     (instantiate-existential ("b"))
     (contrapose "with(b,f,a:points,bet(a,f,b));")
     (backchain "with(h,a:points,a=h);")
     (apply-macete-with-minor-premises symmetry-of-betweeness)
     (apply-macete-with-minor-premises anti-cyclic)
     (apply-macete-with-minor-premises symmetry-of-betweeness))
    (cut-with-single-formula "not coll(f,d,a)")
    (move-to-sibling 1)
    (block 
     (script-comment "`cut-with-single-formula' at (1)")
     (apply-macete-with-minor-premises non-collinear-2-other)
     (instantiate-existential ("c" "b")))
    (cut-with-single-formula "forsome(l:points, l in le(h,r) and bet(d,l,a))")
    (move-to-sibling 1)
    (block 
     (script-comment "`cut-with-single-formula' at (1)")
     (apply-macete-with-minor-premises weak-pasch)
     (instantiate-existential ("f"))
     (apply-macete-with-minor-premises coll-conjunctive-permuter)
     simplify)
    (antecedent-inference "with(p:prop,forsome(l:points,p));")
    (cut-with-single-formula "bet(h,r,l)")
    (move-to-sibling 1)
    (block 
     (script-comment "`cut-with-single-formula' at (1)")
     (apply-macete-with-minor-premises weak-pasch-ordered)
     (instantiate-existential ("f" "a" "d")))
    (cut-with-single-formula "bet(c,r,l)")
    (move-to-sibling 1)
    (block 
     (script-comment "`cut-with-single-formula' at (1)")
     (apply-macete-with-minor-premises nesting-2)
     (instantiate-existential ("h"))
     (force-substitution "c=l" "l=c" (0))
     (block 
      (script-comment "`force-substitution' at (0)")
      (apply-macete-with-minor-premises non-equality-1)
      (instantiate-existential ("d" "a"))
      simplify
      simplify
      (block 
       (script-comment "`instantiate-existential' at (0 3)")
       (apply-macete-with-minor-premises coll-conjunctive-permuter)
       simplify)
      (block 
       (script-comment "`instantiate-existential' at (0 4)")
       (apply-macete-with-minor-premises collinear-flipper-1-2)
       (move-to-ancestor 1)
       (apply-macete-with-minor-premises collinear-all-cases)
       simplify))
     simplify)
    (cut-with-single-formula "not coll(l,c,a)")
    (move-to-sibling 1)
    (apply-macete-with-minor-premises non-collinear)
    (instantiate-existential ("d"))
    (move-to-ancestor 4)
    (block 
     (script-comment "`cut-with-single-formula' at (0)")
     (cut-with-single-formula "not coll(l,a,c)")
     (move-to-sibling 1)
     (block 
      (script-comment "`cut-with-single-formula' at (1)")
      (apply-macete-with-minor-premises non-collinear)
      auto-instantiate-existential
      (block 
       (script-comment "`auto-instantiate-existential' at (0 3)")
       (apply-macete-with-minor-premises coll-conjunctive-permuter)
       simplify)
      (block 
       (script-comment "`auto-instantiate-existential' at (0 4)")
       (apply-macete-with-minor-premises collinear-all-cases)
       simplify))
     (block 
      (script-comment "`cut-with-single-formula' at (0)")
      (cut-with-single-formula "not l=c and not l=a")
      (move-to-sibling 1)
      (block 
       (script-comment "`cut-with-single-formula' at (1)")
       direct-and-antecedent-inference-strategy
       (apply-macete-with-minor-premises distinctness-2-3)
       auto-instantiate-existential)
      (block 
       (script-comment "`cut-with-single-formula' at (0)")
       (cut-with-single-formula "forsome(e:points,e in le(d,r) and bet(c,e,a))")
       (move-to-sibling 1)
       (block 
	(script-comment "`cut-with-single-formula' at (1)")
	(apply-macete-with-minor-premises weak-pasch)
	auto-instantiate-existential
	(block 
	 (script-comment "`auto-instantiate-existential' at (0 0)")
	 (apply-macete-with-minor-premises coll-conjunctive-permuter)
	 simplify)
	(apply-macete-with-minor-premises symmetry-of-betweeness))
       (block 
	(script-comment "`cut-with-single-formula' at (0)")
	(antecedent-inference "with(p:prop,forsome(e:points,p));")
	(cut-with-single-formula "le(d,r)=le(d,f)")
	(move-to-sibling 1)
	(block 
	 (script-comment "`cut-with-single-formula' at (1)")
	 (apply-macete-with-minor-premises le-equality-condition)
	 (apply-macete-with-minor-premises collinear-all-cases)
	 simplify)
	(block 
	 (script-comment "`cut-with-single-formula' at (0)")
	 (antecedent-inference-strategy (10 6 2 1))
	 (incorporate-antecedent "with(e,r,d:points,e in le(d,r));")
	 (backchain "with(f:sets[points],f=f);")
	 direct-and-antecedent-inference-strategy
	 (instantiate-existential ("e"))
	 (block 
	  (script-comment "`instantiate-existential' at (0 0)")
	  (cut-with-single-formula "bet(d,e,f)")
	  (move-to-ancestor 1)
	  (cut-with-single-formula "not d=e")
	  (move-to-sibling 1)
	  (block 
	   (script-comment "`cut-with-single-formula' at (1)")
	   (apply-macete-with-minor-premises inequality-2)
	   (instantiate-existential ("a" "b"
                                                                 
					 "c"))
	   (apply-macete-with-minor-premises collinear-all-cases)
	   simplify)
	  (block 
	   (script-comment "`cut-with-single-formula' at (0)")
	   (incorporate-antecedent "with(e,f,d:points,e in le(d,f));")
	   (unfold-single-defined-constant (0)
                                                                 
					   le)
	   (cut-with-single-formula "not d=f")
	   simplify
	   (cut-with-single-formula "not e=f")
	   (move-to-sibling 1)
	   (block 
	    (script-comment "`cut-with-single-formula' at (1)")
	    (apply-macete-with-minor-premises inequality-2)
	    (instantiate-existential ("b" "c"
                                                                 
					  "a"))
	    simplify
	    (block 
	     (script-comment "`instantiate-existential' at (0 3)")
	     (apply-macete-with-minor-premises coll-conjunctive-permuter)
	     simplify)
	    (block 
	     (script-comment "`instantiate-existential' at (0 4)")
	     (apply-macete-with-minor-premises collinear-all-cases)
	     simplify)
	    (block 
	     (script-comment "`instantiate-existential' at (0 5)")
	     (apply-macete-with-minor-premises collinear-all-cases)
	     simplify))
	   (block 
	    (script-comment "`cut-with-single-formula' at (0)")
	    direct-and-antecedent-inference-strategy
	    (apply-macete-with-minor-premises coll-disjunctive-permuter)
	    simplify)))
	 (apply-macete-with-minor-premises symmetry-of-betweeness))))))
   
   
    )))








 "We next show that a line can intersect at most two sides of a triangle."

(def-theorem line-intersects-at-most-two-sides-of-a-triangle-lemma-1
   "forall(a,b,c,x,y,z:points,   
     not(coll(a,b,c)) and bet(a,x,b) and bet(b,y,c) and bet(c,z,a) implies not(x=y))"
   (theory geometry-2)
   (proof
    (


     direct-and-antecedent-inference-strategy
     (contrapose "with(b,x,a:points,bet(a,x,b));")
     (backchain "with(y,x:points,x=y);")
     (contrapose "with(p:prop,not(p));")
     (apply-macete-with-minor-premises switching)
     (instantiate-existential ("y"))
     (block 
      (script-comment "`instantiate-existential' at (0 0)")
      (apply-macete-with-minor-premises distinctness-1-3)
      auto-instantiate-existential)
     (block 
      (script-comment "`instantiate-existential' at (0 1)")
      (apply-macete-with-minor-premises collinear-flipper-2-3)
      (apply-macete-with-minor-premises switching)
      (instantiate-existential ("b"))
      (block 
       (script-comment "`instantiate-existential' at (0 0)")
       (apply-macete-with-minor-premises distinctness-1-3)
       auto-instantiate-existential
       (instantiate-existential ("b"))
       (move-to-ancestor 1)
       (instantiate-existential ("z")))
      (block 
       (script-comment "`instantiate-existential' at (0 1)")
       (apply-macete-with-minor-premises collinear-all-cases)
       direct-and-antecedent-inference-strategy)
      (block 
       (script-comment "`instantiate-existential' at (0 2)")
       (apply-macete-with-minor-premises collinear-all-cases)
       direct-and-antecedent-inference-strategy))
     (block 
      (script-comment "`instantiate-existential' at (0 2)")
      (apply-macete-with-minor-premises collinear-all-cases)
      direct-and-antecedent-inference-strategy)
     )))

(comment
 (def-theorem line-intersects-at-most-two-sides-of-a-triangle
    "forall(a,b,c,x,y,z:points,  (not(coll(a,b,c))
     and bet(a,x,b) and bet(b,y,c) and bet(c,z,a)) implies
      (not(x=y) and not(x=z) and not(y=z) and not(coll(x,y,z))))"
    (theory geometry-2)
    (proof
     (


   
      direct-and-antecedent-inference-strategy
      (block 
       (script-comment "`direct-and-antecedent-inference-strategy' at (0 0 0 0)")
       (apply-macete-with-minor-premises line-intersects-at-most-two-sides-of-a-triangle-lemma-1)
       (instantiate-existential ("z" "c" "b" "a")))
      (block 
       (script-comment "`direct-and-antecedent-inference-strategy' at (0 0 1 0)")
       (apply-macete-with-minor-premises line-intersects-at-most-two-sides-of-a-triangle-lemma-1)
       (instantiate-existential ("y" "c" "a" "b"))
       (apply-macete-with-minor-premises collinear-flipper-1-2)
       (apply-macete-with-minor-premises symmetry-of-betweeness)
       (apply-macete-with-minor-premises symmetry-of-betweeness)
       (apply-macete-with-minor-premises symmetry-of-betweeness))
      (block 
       (script-comment "`direct-and-antecedent-inference-strategy' at (0 0 2 0)")
       (apply-macete-with-minor-premises line-intersects-at-most-two-sides-of-a-triangle-lemma-1)
       (instantiate-existential ("x" "a" "c" "b"))
       (apply-macete-with-minor-premises collinear-flipper-1-2)
       (apply-macete-with-minor-premises collinear-flipper-1-3))
      (contrapose "with(c,b,a:points,not(coll(a,b,c)));")
      (apply-macete-with-minor-premises switching)

      ))))

