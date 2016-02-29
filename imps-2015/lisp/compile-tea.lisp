(mapc #'(lambda (x) (load (format nil "/home/vc/jt/sys/lisp/~A.lisp" x)))
	'(
	  "packages"
	  "tea-implementation"
	  "tea"
	  "basic"
	  "supplements"
	  "sets"
	  "special-forms"
	  "operations"
	  "structures"
	  "definitions"
	  "ports"
	  "wrappers"
	  "hash"
	  "filesystem"
	  "initialization"
	  "repl"))

(mapc #'(lambda (x) (compile-file (format nil "/home/vc/jt/sys/lisp/~A.lisp" x)))
	'(
	  "packages"
	  "tea-implementation"
	  "tea"
	  "basic"
	  "supplements"
	  "sets"
	  "special-forms"
	  "operations"
	  "structures"
	  "definitions"
	  "ports"
	  "wrappers"
	  "hash"
	  "filesystem"
	  "initialization"
	  "repl"))