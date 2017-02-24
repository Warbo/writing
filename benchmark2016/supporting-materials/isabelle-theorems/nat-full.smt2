;; USING Z, S, plus, times, exp

;; (a * m) + m = (a + (S 0)) * m
(assert-not (forall ((a Nat) (m Nat))
  (= (plus (times a m) m)
     (times (plus a (constructor-S constructor-Z)) m))))

;; m + (a * m) = (a + (S 0)) * m
(assert-not (forall ((a Nat) (m Nat))
  (= (plus m (times a m))
     (times (plus a (constructor-S constructor-Z)) m))))

;; m+m=((S0)+(S0))*m
(assert-not (forall ((m Nat))
  (= (plus m m)
     (times (plus (constructor-S constructor-Z) (constructor-S constructor-Z)) m))))

;; (lx*ly)*(rx*ry)=lx*(ly*(rx*ry))
(assert-not (forall ((lx Nat) (ly Nat) (rx Nat) (ry Nat))
  (= (times (times lx ly) (times rx ry))
     (times lx (times ly (times rx ry))))))

;; lx*(rx*ry)=(lx*rx)*ry
(assert-not (forall ((lx Nat) (rx Nat) (ry Nat))
  (= (times lx (times rx ry))
     (times (times lx rx) ry))))

;; (lx*ly)*rx=(lx*rx)*ly
(assert-not (forall ((lx Nat) (ly Nat) (rx Nat))
  (= (times (times lx ly) rx)
     (times (times lx rx) ly))))

;; x^((S(S0)) * n) = (x^n)*(x^n)
(assert-not (forall ((x Nat) (n Nat))
  (= (exp x (times (constructor-S (constructor-S constructor-Z)) n))
     (times (exp x n) (exp x n)))))

;; x^((S(S(S0)))*n)=x*((x^n)*(x^n))
(assert-not (forall ((x Nat) (n Nat))
  (= (exp x (times (constructor-S (constructor-S (constructor-S constructor-Z))) n))
     (times x (times (exp x n) (exp x n))))))

;; (lx*ly)*(rx*ry)=(lx*rx)+(ly*ry)
(assert-not (forall ((lx Nat) (ly Nat) (rx Nat) (ry Nat))
  (= (times (times lx ly) (times rx ry))
     (plus (times lx rx) (times ly ry)))))

;; (a+b)+(c+d)=(a+c)+(b+d)
(assert-not (forall ((a Nat) (b Nat) (c Nat) (d Nat))
  (= (plus (plus a b) (plus c d))
     (plus (plus a c) (plus b d)))))

;; a+(c+d)=(a+c)+d
(assert-not (forall ((a Nat) (c Nat) (d Nat))
  (= (plus a (plus c d))
     (plus (plus a c) d))))

;; (a+b)+c=(a+c)+b
(assert-not (forall ((a Nat) (b Nat) (c Nat))
  (= (plus (plus a b) c)
     (plus (plus a c) b))))

;; a*(S0)=a
(assert-not (forall ((a Nat))
  (= (times a (constructor-S constructor-Z))
     a)))

;; (S0)*a=a
(assert-not (forall ((a Nat))
  (= (times (constructor-S constructor-Z) a)
     a)))

;; (x^q)*x=x^(Sq)
(assert-not (forall ((x Nat) (q Nat))
  (= (times (exp x q) x)
     (exp x (constructor-S q)))))

;; x*(x^q)=x^(Sq)
(assert-not (forall ((x Nat) (q Nat))
  (= (times x (exp x q))
     (exp x (constructor-S q)))))

;; x*x=x^(S(S0))
(assert-not (forall ((x Nat))
  (= (times x x)
     (exp x (constructor-S (constructor-S constructor-Z))))))

;; x^(S0)=x
(assert-not (forall ((x Nat))
  (= (exp x (constructor-S constructor-Z))
     x)))

;; (lx*ly)*(rx*ry)=rx*((lx*ly)*ry)
(assert-not (forall ((lx Nat) (ly Nat) (rx Nat) (ry Nat))
  (= (times (times lx ly) (times rx ry))
     (times rx (times (times lx ly) ry)))))

;; x+0=x
(assert-not (forall ((x Nat))
  (= (plus x constructor-Z)
     x)))

;; x*0=0
(assert-not (forall ((x Nat))
  (= (times x constructor-Z)
     constructor-Z)))

;; (S0)^x=S0
(assert-not (forall ((x Nat))
  (= (exp (constructor-S constructor-Z) x)
     (constructor-S constructor-Z))))

;; y+(Sz)=S(y+z)
(assert-not (forall ((z Nat))
  (= (plus y (constructor-S z))
     (constructor-S (plus y z)))))

;; y+x=x+y
(assert-not (forall ((y Nat) (y Nat))
  (= (plus y x)
     (plus x y))))

;; (x+y)+z=x+(y+z)
(assert-not (forall ((x Nat) (y Nat) (z Nat))
  (= (plus (plus x y) z)
     (plus x (plus y z)))))

;; y+(x+z)=x+(y+z)
(assert-not (forall ((x Nat) (y Nat) (z Nat))
  (= (plus y (plus x z))
     (plus x (plus y z)))))

;; (x+y)*z=(x*z)+(y*z)
(assert-not (forall ((x Nat) (y Nat) (z Nat))
  (= (times (plus x y) z)
     (plus (times x z) (times y z)))))

;; x*(Sz)=x+(x*z)
(assert-not (forall ((x Nat) (z Nat))
  (= (times x (constructor-S z))
     (plus x (times x z)))))

;; x*(y+z)=(x*y)+(x*z)
(assert-not (forall ((x Nat) (y Nat) (z Nat))
  (= (times x (plus y z))
     (plus (times x y) (times x z)))))

;; y*x=x*y
(assert-not (forall ((x Nat) (y Nat))
  (= (times y x)
     (times x y))))

;; (x*y)*z=x*(y*z)
(assert-not (forall ((x Nat) (y Nat) (z Nat))
  (= (times (times x y) z)
     (times x (times y z)))))

;; y*(x*z)=x*(y*z)
(assert-not (forall ((x Nat) (y Nat) (z Nat))
  (= (times y (times x z))
     (times x (times y z)))))

;; (x*y)^z=(x^z)*(y^z)
(assert-not (forall ((x Nat) (y Nat) (z Nat))
  (= (exp (times x y) z)
     (times (exp x z) (exp y z)))))

;; x^(y+z)=(x^y)*(x^z)
(assert-not (forall ((x Nat) (y Nat) (z Nat))
  (= (exp x (plus y z))
     (times (exp x y) (exp x z)))))

;; (x^y)^z=x^(y*z)
(assert-not (forall ((x Nat) (y Nat) (z Nat))
  (= (exp (exp x y) z)
     (exp x (times y z)))))
