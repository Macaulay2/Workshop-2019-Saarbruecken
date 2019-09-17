restart
needsPackage "NumericalAlgebraicGeometry"
debug loadPackage("DualSpaces", Reload => true)

--Define ideal and sample points on it
R = CC[x,y,t]
I = ideal(x^2 - t*y, y^2)
nv = numericalIrreducibleDecomposition(I, Software => BERTINI)
Wset = nv#1#0
pts = toList(1..20) / (i -> matrix sample(Wset))

--Compute Noetherian Operators on each point
noethOpsAtPoints = pts / (p-> numNoethOps(I, p, DependentSet => {x,y}))
netList noethOpsAtPoints

-- First and second noeth op are fine,
-- they are not a function of t

-- consider the third one. The coefficient of dy
-- should be a function of t
coeffs = (transpose noethOpsAtPoints)#2 / coefficient_dy / (x -> sub(x,CC))

-- we guess that it is at most of degree 4
numBasis = matrix {{1,t,t^2,t^3,t^4}}
denBasis = numBasis

rationalInterpolation(pts, coeffs, numBasis, denBasis, Tolerance => 0.00001)

-- The coefficient of dy is thus 1/.5t, or t/.5t^2 etc.
-- Clearing denominators, we conclude that the third noetherian operator
-- is 1/2 dx^2 + dy

-- For the last operator, we compute the coefficient of
-- dx*dy as a rational function of t
coeffs = (transpose noethOpsAtPoints)#3 / coefficient_(dy*dx) / (x -> sub(x,CC))

rationalInterpolation(pts, coeffs, numBasis, denBasis)

-- Clearing denominators we get
-- .16667t dx^3 + dx*dy




--Define ideal and sample points on it
S = QQ[x,y,s]
J = ideal(random(4,S), random(4,S))
noethOps(J^2, DegreeLimit => 2)

R = CC[x,y,s]
I = (sub(J^2, R))
nv = numericalIrreducibleDecomposition(I, Software => BERTINI)
Wset = nv#1#0
pts = toList(1..20) / (i -> matrix sample(Wset))

--Compute Noetherian Operators on each point
noethOpsAtPoints = pts / (p-> numNoethOps(I, p, DependentSet => {x,y}, Tolerance => 0.001))

-- This is bad.

-- Let's refine the points







-- First and second noeth op are fine,
-- they are not a function of t

-- consider the third one. The coefficient of dy
-- should be a function of t
coeffs = (transpose noethOpsAtPoints)#2 / coefficient_dy / (x -> sub(x,CC))


-- we guess that it is at most of degree 4
numBasis = matrix {{1,t,t^2,t^3,t^4}}
denBasis = numBasis

rationalInterpolation(pts, coeffs, numBasis, denBasis, Tolerance => 0.00001)

-- The coefficient of dy is thus 1/.5t, or t/.5t^2 etc.
-- Clearing denominators, we conclude that the third noetherian operator
-- is 1/2 dx^2 + dy

-- For the last operator, we compute the coefficient of
-- dx*dy as a rational function of t
coeffs = (transpose noethOpsAtPoints)#3 / coefficient_(dy*dx) / (x -> sub(x,CC))

rationalInterpolation(pts, coeffs, numBasis, denBasis)

-- Clearing denominators we get
-- .16667t dx^3 + dx*dy