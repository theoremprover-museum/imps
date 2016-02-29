(bind (((proof-log-port) '#f))
      (include-files
       (files (imps theories/cardinality/cardinality-supplements)
	      (imps theories/cardinality/combinatorics))))

(include-files 
 (files "~jt/imps/theories/geometry/presentation.t"
	"~jt/imps/theories/geometry/cardinality.t"
	"~jt/imps/theories/geometry/sylvester.t"))
 