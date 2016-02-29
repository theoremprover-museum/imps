(load-section sequences)

(include-files
  (files (imps theories/networks/addresses)))

;;; Protocols

(def-language protocol-language
  (base-types protocols tcp%flags)
  (constants

   (udp protocols)
   (tcp protocols)
   (icmp protocols)
   (igmp protocols)

   (urg tcp%flags)
   (ack tcp%flags)
   (psh tcp%flags)
   (rst tcp%flags)
   (syn tcp%flags)
   (fin tcp%flags)

   ))

(def-theory protocol-theory
  (language protocol-language)
  (component-theories h-o-real-arithmetic)
  (distinct-constants 
   (udp tcp icmp igmp)
   (urg ack psh rst syn fin)
   ))


;;; Data

(def-language data-language
  (base-types data))

(def-theory data-theory
  (language data-language)
  (component-theories h-o-real-arithmetic))


;;; Datagrams

(def-theory datagrams
  (component-theories protocol-theory data-theory octets))

(def-atomic-sort ports
  "lambda(n:nn, truth)"
  (theory datagrams))

(def-cartesian-product datagrams
  (addresses addresses ports ports protocols "sets[tcp%flags]" data)
  (constructor make%datagram)
  (accessors source%address
	     destination%address
	     source%port
	     destination%port
             protocol
             tcp%flag%set
	     content)
  (theory datagrams))



