;% Copyright (c) 1990-1994 The MITRE Corporation
;% 
;% Authors: W. M. Farmer, J. D. Guttman, F. J. Thayer
;%   
;% The MITRE Corporation (MITRE) provides this software to you without
;% charge to use, copy, modify or enhance for any legitimate purpose
;% provided you reproduce MITRE's copyright notice in any copy or
;% derivative work of this software.
;% 
;% This software is the copyright work of MITRE.  No ownership or other
;% proprietary interest in this software is granted you other than what
;% is granted in this license.
;% 
;% Any modification or enhancement of this software must identify the
;% part of this software that was modified, by whom and when, and must
;% inherit this license including its warranty disclaimers.
;% 
;% MITRE IS PROVIDING THE PRODUCT "AS IS" AND MAKES NO WARRANTY, EXPRESS
;% OR IMPLIED, AS TO THE ACCURACY, CAPABILITY, EFFICIENCY OR FUNCTIONING
;% OF THIS SOFTWARE AND DOCUMENTATION.  IN NO EVENT WILL MITRE BE LIABLE
;% FOR ANY GENERAL, CONSEQUENTIAL, INDIRECT, INCIDENTAL, EXEMPLARY OR
;% SPECIAL DAMAGES, EVEN IF MITRE HAS BEEN ADVISED OF THE POSSIBILITY OF
;% SUCH DAMAGES.
;% 
;% You, at your expense, hereby indemnify and hold harmless MITRE, its
;% Board of Trustees, officers, agents and employees, from any and all
;% liability or damages to third parties, including attorneys' fees,
;% court costs, and other related costs and expenses, arising out of your
;% use of this software irrespective of the cause of said liability.
;% 
;% The export from the United States or the subsequent reexport of this
;% software is subject to compliance with United States export control
;% and munitions control restrictions.  You agree that in the event you
;% seek to export this software or any derivative work thereof, you
;% assume full responsibility for obtaining all necessary export licenses
;% and approvals and for assuring compliance with applicable reexport
;% restrictions.
;% 
;% 
;% COPYRIGHT NOTICE INSERTED: Mon Apr 11 11:42:27 EDT 1994


(herald some-formulas)


(lset 1stnsquares
      (qr "forall([[[n],zz]],0<=n implies sum(0,n,lambda([[[j],zz]],j^2))=n*(n+1)*(2*n+1)/6)")
)

(lset bogus-1stnsquares
      (qr "forall([[[n],zz]],0<=n implies sum(0,n,lambda([[[j],zz]],j^2))=n*(n+1)*(2*n+1)/5)")
)

(lset 1stncubes
      (qr "forall([[[n],zz]],0<=n implies sum(0,n,lambda([[[j],zz]],j^3))=((n*(n+1))/2)^2)"))

(lset 1stn
      (qr "forall([[[m],zz]],0<=m implies sum(0,m,lambda([[[j],zz]],j))=m*(m+1)/2)"))

(lset 1stnsixths
      (qr "forall([[[n],zz]],0<=n implies sum(0,n,lambda([[[j],zz]],j^6))
=
 n^7/7 + n^6/2 + n^5/2 -n^3/6 +n/42)"))

(lset 1stntenths
      (qr "forall([[[n],zz]],0<=n implies sum(0,n,lambda([[[j],zz]],j^10))
=
 n^11/11 + n^10/2 + (5*n^9)/6 - n^7 + n^5 - n^3/2 + (5*n/66))"))

(lset var-1stntenths
      (qr "forall([[[n],zz]],0<=n implies 66*sum(0,n,lambda([[[j],zz]],j^10))
=
 6*n^11 + 33*n^10 + 11*(5*n^9) - 66*n^7 + 66*n^5 - 33*n^3 + (5*n))"))

(lset binomial-thm
      (qr "forall([[[a,b],rr]], (not(a=0) and not(b=0)) implies forall([[[m],zz]],1<=m  implies (a+b)^m=sum(0,m,lambda([[[k],zz]],comb(m,k)*a^(m-k)*b^k))))"))


(lset associativity-for-sum
      (qr "forall([[[f,g],[zz,rr]],[[m,n],zz]],m<=n
implies sum(m,n,lambda([[[k],zz]],f(k)+g(k)))==sum(m,n,f)+sum(m,n,g))"))

(lset associativity-for-product
      (qr "forall([[[f,g],[zz,rr]],[[m,n],zz]],m<=n
implies prod(m,n,lambda([[[k],zz]],f(k)*g(k)))==prod(m,n,f)*prod(m,n,g))"))

(lset bogus-associativity-for-product
      (qr "forall([[[f,g],[zz,rr]],[[m,n],zz]],m<=n
implies prod(m,n,lambda([[[k],zz]],f(k)*g(k)))=prod(m,n,f)*prod(m,n,g))"))

(lset comb-ident
      (qr "forall([[[k,m],zz]],(1<=k and k<=m) implies comb(1+m,k)=comb(m,k-1)+comb(m,k))"))

(lset monotonicity-for-sum
      (qr "forall([[[f,g],[zz,rr]]],
forall([[[x],zz]],f(x)<=g(x))
 implies
forall([[[m],zz]],
0<=m
 implies
sum(0,m,lambda([[[k],zz]],f(k)))<=sum(0,m,lambda([[[k],zz]],g(k)))))"))

(lset chebyshevs-inequality
      (qr "forall([[[f],[rr,rr]]],forall([[[x],rr]],0<=f(x)) implies
forall([[[m],zz]],
0<=m
 implies
forall([[[r],rr]],r*sum(0,m,lambda([[[k],zz]],if(r<=f(k),1,0)))<=sum(0,m,lambda([[[k],zz]],f(k))))))"))


(lset triangle-inequality
      (qr "forall([[[x,y,z],rr]],abs(x-z)<=abs(x-y)+abs(y-z))"))

(lset linearity-of-sum
      (qr "forall([[[f,g],[zz,rr]],[[m,n],zz],[[c,d],rr]], sum(m,n,lambda([[[k],zz]],c*f(k)+d*g(k)))==c*sum(m,n,f)+d*sum(m,n,g))"))

(lset invariance-of-sum
      (qr "forall([[[f],[zz,rr]],[[m,n,p],zz]], sum(m,n,f)==sum(m+p,n+p,lambda([[[k],zz]],f(k-p))))"))

(lset square-root-for-negatives
      (qr "forall([[[w],rr]], w<0 implies not(#(sqrt(w))))"))

;;;(lset 0-limit
;;;      (qr "lim(lambda([[[j],zz]],1/j)) = 0"))


(lset telescoping-sum
      (qr "forall([[[a,b],rr],[[n,k],zz]],not(a=0) and not(b=0) and 0<=n and 0<=k and k<=n implies a^(k+1)*b^(n-k)-b^(n+1)=sum(0,k,lambda([[[i],zz]],a^i*b^(n-i)))*(a-b))"))

