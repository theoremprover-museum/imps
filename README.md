# IMPS

IMPS is an Interactive Mathematical Proof System developed by
W. M. Farmer, J. D. Guttman, and F. J. Thayer at The MITRE Corporation
during 1990-1993.  It is intended to provide mechanical support for
traditional mathematical techniques and styles of practice.  The
system consists of a library of mathematics plus facilities for
developing axiomatic theories, proving conjectures, and performing
rigorous symbolic computations.  IMPS has proven to be an effective
medium for formalizing classical mathematics, particularly
mathematical analysis.  Available to the public without fee, it was
first released on June 11, 1993.

IMPS is distinguished by its method of organizing mathematics, its
logic, and its style of proof.  IMPS emphasizes the "little theories"
version of the axiomatic method, as opposed to the "big theory"
version.  In the little theories approach, reasoning is distributed
over a network of theories linked by theory interpretations.  The
little theories approach is a powerful technique for exploiting the
interconnectedness of mathematics.  

The underlying logic of IMPS is a version of simple type theory.
Equipped with special machinery for reasoning about functions, it has
proven to be highly effective for formalizing many kinds of
mathematics.  It is exceptional in that partial functions like
division and undefined terms like 3/0 can be directly represented and
manipulated without compromising the basic principles of classical
predicate logic.

IMPS proofs are a blend of calculation and deduction.  Low-level
inferences can be performed with calculation tools that simplify
expressions and apply theorems (via procedures called macetes).
High-level inferences are performed by applying proof commands or by
executing proof scripts that apply a sequence of proof commands in an
intelligent manner.

The theory library contains significant portions of logic, algebra,
and analysis with over 1300 replayable proofs.  The source code of the
system (minus the theory library) consists of over 70,000 lines of
Lisp code (Common Lisp and GNU Emacs).
