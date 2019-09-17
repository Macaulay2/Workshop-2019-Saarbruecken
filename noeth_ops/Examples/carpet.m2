restart
needsPackage "NumericalAlgebraicGeometry"
needsPackage "Bertini"
debug loadPackage("DualSpaces", Reload => true)

needsPackage "K3Carpets"
I = carpet(3,2, Characteristic => 0)
R = ring I
noethOps I

S = CC monoid R
K = sub(I, S)
J = sub(radical I, S)
nv = numericalIrreducibleDecomposition (J, Software => BERTINI)
pts = nv#3#0#Points

nv = numericalIrreducibleDecomposition (J, Software => BERTINI)
pts = nv#3#0#Points | pts

sample(nv#3#0)

L = pts / matrix / (p -> numNoethOps(K, p, DegreeLimit => 2))
vals = L / (i -> coefficient(dy_1,i#1))

rationalInterpolation(pts, vals / (i->sub(i,CC)), basis(0,2,S), basis(0,2,S))

rationalInterpolation(pts, vals / (i->sub(i,CC)), matrix{{S_0*S_2,S_3*S_4}}, matrix{{S_0*S_6}}, Tolerance => 1e-6)
foo = rationalInterpolation(pts, vals / (i->sub(i,CC)), basis(0,1,S), basis(0,1,S), Tolerance => 1e-6)
wrap("~",150, netList entries (foo#0 || foo#1))

apply(20, sample(nv#3#0))
