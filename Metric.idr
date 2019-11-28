
%default total

record Metric where
  constructor MkMetric
  carrierSet   : Type
  distance     : carrierSet -> carrierSet -> Nat
  distanceSym  : (a, b : carrierSet) -> distance a b = distance b a
  distanceZero : (a : carrierSet)    -> distance a a = Z
  distanceTri  : (a, b, x : carrierSet) -> distance a b `LTE` (distance a x + distance x b)


absoluteDiff : Nat -> Nat -> Nat
absoluteDiff n Z = n
absoluteDiff Z n = n
absoluteDiff (S n) (S l) = absoluteDiff n l

absLeftZero : (a : Nat) -> absoluteDiff 0 a = a
absLeftZero Z = Refl
absLeftZero (S k) = Refl

absRightZero : absoluteDiff a 0 = a
absRightZero {a = Z} = Refl
absRightZero {a = (S k)} = Refl

triangleDiff : absoluteDiff (absoluteDiff a b) (absoluteDiff b c) `LTE` absoluteDiff a c
triangleDiff {a = Z} {b = b} {c = c} =
  rewrite absLeftZero c in
  rewrite absLeftZero b in ?whut
triangleDiff {a = (S k)} {b = b} {c = c} = ?triangleDiff_rhs_2

natDiffSym : {a, b : Nat} -> absoluteDiff a b = absoluteDiff b a
natDiffSym {a = Z} {b = b} = absLeftZero b
natDiffSym {a = (S k)} {b = Z} = absRightZero
natDiffSym {a = (S k)} {b = (S j)} = natDiffSym {a=k} {b=j}

natDiffSame : {a : Nat} -> absoluteDiff a a = Z
natDiffSame {a = Z} = Refl
natDiffSame {a = (S k)} = natDiffSame {a=k}

succLTEDiff : absoluteDiff (S a) b = S (absoluteDiff a b)
succLTEDiff {a = Z} {b = Z} = Refl
succLTEDiff {a = Z} {b = (S k)} = ?succLTEDiff_rhs_4
succLTEDiff {a = (S k)} {b = b} = ?succLTEDiff_rhs_2

diffLTESum : absoluteDiff a b `LTE` a + b
diffLTESum {a = Z} {b = b} = rewrite absLeftZero b in lteRefl
diffLTESum {a = (S k)} {b = b} = let rec = diffLTESum {a=k} {b=b} in
                             rewrite succLTEDiff {a=k} {b=b} in LTESucc rec

eqImpliesLte : a = b -> a `LTE` b
eqImpliesLte Refl {a = a} {b = a} = lteRefl


natDiffTri : (a, b, x : Nat) -> absoluteDiff a b `LTE` (absoluteDiff a x + absoluteDiff x b)
natDiffTri a b Z = rewrite absLeftZero b in diffLTESum
natDiffTri a b (S k) = let rec = natDiffTri a b k in ?whattheheck

natMetric : Metric
natMetric = MkMetric
  Nat
  absoluteDiff
  (\x, y => natDiffSym)
  (\_ => natDiffSame)
  (natDiffTri)


||| from an existring metric m and a function from carrierSet z to y, build a new metric space
newMetric : (f : z -> y) -> (m : Metric) -> carrierSet m = y -> Metric
newMetric f {z} (MkMetric carrierSet distance distanceSym distanceZero distanceTri) Refl =
  MkMetric z newDistance distanceSymetric (\a => distanceZero (f a)) newDistanceTri
  where newDistance : z -> z -> Nat
        newDistance a b = distance (f a) (f b)
        distanceSymetric : (a , b : z) -> distance (f a) (f b) = distance (f b) (f a)
        distanceSymetric a b = distanceSym (f a) (f b)
        newDistanceTri : (a, b, x : z) -> newDistance a b `LTE` (newDistance a x + newDistance x b)
        newDistanceTri a b x = distanceTri (f a) (f b) (f x)
