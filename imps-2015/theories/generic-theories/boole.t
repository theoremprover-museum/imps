;;; No required files

(def-atomic-sort boole
  "lambda(n:zz, n = [-1] or n = 1)"
  (theory h-o-real-arithmetic))

(def-constant true%val
  "1"
  (sort "boole")
  (theory h-o-real-arithmetic))

(def-constant false%val
  "[-1]"
  (sort "boole")
  (theory h-o-real-arithmetic))

(def-constant is%true
  "lambda(b:boole, b = true%val)"
  (theory h-o-real-arithmetic))

(def-constant is%false
  "lambda(b:boole, b = false%val)"
  (theory h-o-real-arithmetic))

(def-theorem true%val-is-true
  "is%true(true%val) iff truth"
  (usages rewrite)
  (theory h-o-real-arithmetic)
  (proof
   (

    (unfold-single-defined-constant-globally is%true)

    )))

(def-theorem false%val-is-not-true
  "is%true(false%val) iff falsehood"
  (usages rewrite)
  (theory h-o-real-arithmetic)
  (proof
   (
    
    (unfold-single-defined-constant-globally is%true)
    unfold-defined-constants

    )))

(def-theorem true%val-is-not-false
  "is%false(true%val) iff falsehood"
  (usages rewrite)
  (theory h-o-real-arithmetic)
  (proof
   (

    (unfold-single-defined-constant-globally is%false)
    unfold-defined-constants

    )))

(def-theorem false%val-is-false
  "is%false(false%val) iff truth"
  (usages rewrite)
  (theory h-o-real-arithmetic)
  (proof
   (
    
    (unfold-single-defined-constant-globally is%false)

    )))
