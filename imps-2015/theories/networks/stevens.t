(include-files
  (files (imps theories/networks/networks)))


;; Make copy of Networks theory named Pre-Stevens

(define (stevens-renamer name)
  (concatenate-symbol 's% name))

(def-theory-instance pre-stevens
  (source networks)
  (target the-kernel-theory)
  (translation the-kernel-translation)
  (fixed-theories octets)
  (renamer stevens-renamer)
  (new-translation-name networks-to-pre-stevens))


;; Specify hosts and single physical networks

(def-language stevens-language
  (embedded-language pre-stevens)
  (constants 

   (aix     s%hosts)
   (solaris s%hosts)
   (gemini  s%hosts)
   (gateway s%hosts)
   (netb    s%hosts)
   (slip    s%hosts)
   (bsdi    s%hosts)
   (sun     s%hosts)
   (svr4    s%hosts)

   (ethernet1 s%spnets)
   (ethernet2 s%spnets)
   (slip1     s%spnets)
   (slip2     s%spnets)
   (internet  s%spnets)

   ))


;; Assign interfaces, spnet addresses, and spnet masks

(def-theory stevens
  (language stevens-language)
  (component-theories pre-stevens)
  (distinct-constants 
   (aix solaris gemini gateway netb slip bsdi sun svr4)
   (ethernet1 ethernet2 slip1 slip2 internet))
  (axioms

   (s_iface_relation-axiom
    "s%iface%relation(aix,ethernet1)
      and
     s%iface%relation(solaris,ethernet1)
      and
     s%iface%relation(gemini,ethernet1)
      and
     s%iface%relation(gateway,ethernet1)
      and
     s%iface%relation(netb,ethernet1)
      and
     s%iface%relation(bsdi,ethernet2)
      and
     s%iface%relation(sun,ethernet2)
      and
     s%iface%relation(svr4,ethernet2)
      and
     s%iface%relation(slip,slip1)
      and
     s%iface%relation(bsdi,slip1)
      and
     s%iface%relation(netb,slip2)
      and
     s%iface%relation(sun,slip2)
      and
     s%iface%relation(gateway,internet)")

   (s_address_relation-axiom
    "s%address%relation(s%make%pre%iface(aix,ethernet1),
                        make%address(140#8,252#8,1#8,92#8))
      and
     s%address%relation(s%make%pre%iface(solaris,ethernet1),
                        make%address(140#8,252#8,1#8,32#8))
      and
     s%address%relation(s%make%pre%iface(gemini,ethernet1),
                        make%address(140#8,252#8,1#8,11#8))
      and
     s%address%relation(s%make%pre%iface(gateway,ethernet1),
                        make%address(140#8,252#8,1#8,4#8))
      and
     s%address%relation(s%make%pre%iface(netb,ethernet1),
                        make%address(140#8,252#8,1#8,183#8))
      and
     s%address%relation(s%make%pre%iface(bsdi,ethernet2),
                        make%address(140#8,252#8,13#8,35#8))
      and
     s%address%relation(s%make%pre%iface(sun,ethernet2),
                        make%address(140#8,252#8,13#8,33#8))
      and
     s%address%relation(s%make%pre%iface(svr4,ethernet2),
                        make%address(140#8,252#8,13#8,34#8))
      and
     s%address%relation(s%make%pre%iface(slip,slip1),
                        make%address(140#8,252#8,13#8,65#8))
      and
     s%address%relation(s%make%pre%iface(bsdi,slip1),
                        make%address(140#8,252#8,13#8,66#8))
      and
     s%address%relation(s%make%pre%iface(sun,slip2),
                        make%address(140#8,252#8,1#8,29#8))
      and
     s%address%relation(s%make%pre%iface(gateway,internet),
                        make%address(140#8,252#8,104#8,1#8))")

   (s_mask_relation-axiom
    "s%mask%relation(s%make%pre%iface(aix,ethernet1),
                     make%address(255#8,255#8,255#8,0#8))
      and
     s%mask%relation(s%make%pre%iface(solaris,ethernet1),
                     make%address(255#8,255#8,255#8,0#8))
      and
     s%mask%relation(s%make%pre%iface(gemini,ethernet1),
                     make%address(255#8,255#8,255#8,0#8))
      and
     s%mask%relation(s%make%pre%iface(gateway,ethernet1),
                     make%address(255#8,255#8,255#8,0#8))
      and
     s%mask%relation(s%make%pre%iface(netb,ethernet1),
                     make%address(255#8,255#8,255#8,0#8))
      and
     s%mask%relation(s%make%pre%iface(bsdi,ethernet2),
                     make%address(255#8,255#8,255#8,224#8))
      and
     s%mask%relation(s%make%pre%iface(sun,ethernet2),
                     make%address(255#8,255#8,255#8,224#8))
      and
     s%mask%relation(s%make%pre%iface(svr4,ethernet2),
                     make%address(255#8,255#8,255#8,224#8))
      and
     s%mask%relation(s%make%pre%iface(slip,slip1),
                     make%address(255#8,255#8,255#8,224#8))
      and
     s%mask%relation(s%make%pre%iface(bsdi,slip1),
                     make%address(255#8,255#8,255#8,224#8))
      and
     s%mask%relation(s%make%pre%iface(sun,slip2),
                     make%address(255#8,255#8,255#8,0#8))")

   ))





