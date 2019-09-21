newPackage(
    "MMPSurfaces",
    Version => "0.1",
    Date => "September 20, 2019",
    Authors => 
    {
	{
	    Name => "Isabel Stenger",
	    Email => "stenger@math.uni-sb.de"
	},
        {
	    Name => "Rémi Bignalet-Cazalet",
	    Email => "bignalet@dima.unige.it"
	},
        {
	    Name => "Sascha Blug",
	    Email => "blug@math.uni-sb.de"
	}
    },
    Headline => "Birational classification of smooth surfaces",
    DebuggingMode => false
)

export{
    "geoGenus", 
    "secGenus",
    "irregularity", 
    "intersectionNumber", 
    "eulerNumber", 
    "invariants", 
    "adjunctionMap",
    "dimensionOfTargetSpace",
    "imageUnderAdjunctionMap", 
    "exceptLocus", 
    "kodairaDimension",
    "kodairaFast",
    "kodairaSlow", 
    "classifyKodairaNeg",
    "classifyKodaira0", 
    "classifyKodaira1",
    "classifyKodaira2",
    "classifyKodairaExceptional",
    "classify"
}

undocumented{
    "kodairaFast",
    "kodairaSlow",
    "classifyKodairaNeg",
    "classifyKodaira0", 
    "classifyKodaira1",
    "classifyKodaira2",
    "classifyKodairaExceptional"
}

needsPackage "Divisor"
needsPackage "Cremona"










---------------------------------------------------
----- PART 1: COMPUTATION OF BASIC INVARIANTS -----
---------------------------------------------------



-- computes the geometric genus of X

geoGenus = method();
geoGenus (Ideal) := (X) ->
(
    if pdim (betti res X) == 2 then (
    	S := ring X;
    	resX := res X;
    	dualresX := Hom(resX, S^{-dim S})[-2];
    	(F0,F1,F2) := (dualresX_0, dualresX_1, dualresX_2);
    	return rank source basis(0,F0) - rank source basis(0,F1) + rank source basis(0,F2);
    );
    R := ring X;
    OX0 := R^1/X;
    OX := sheaf OX0;
    omegaX0 := Ext^(codim X) (OX0, R^{-dim R});
    omegaX := sheaf omegaX0;
    rank HH^0(omegaX)
);



-- computes the sectional genus of X

secGenus = method();
secGenus (Ideal) := (X) ->
(
    R := ring X;
    genus (ideal random(1, R) + X)
)



-- computes the irregularity of X

irregularity = method();
irregularity (Ideal) := (X) ->
(
    R := ring X;
    d := degree X;
    OX0 := R^1/X;
    OX := sheaf OX0;
    rank HH^1(OX)
);



-- computes K_X^2

intersectionNumber = method();
intersectionNumber (Ideal) := (X) ->
(
    R := ring X;
    if dim ring X == 5 and dim X == 3 then (
    	d := degree X;
    	q := irregularity(X);
    	g := geoGenus(X);
    	e := 1 - q + g;
    	p := genus (ideal random(1, R) + X);
    	return lift(6*e+1/2*(d^2-5*d-10*(p-1)),ZZ)
     ) else (
	  OX0 := R^1/X;
	  OX := sheaf OX0;
	  omegaX0 := Ext^(codim X) (OX0, R^{-dim R});	
	  omegaX := sheaf omegaX0;
     	  dualSheaf := sheaf(Hom(omegaX0,OX0));
	  return euler(OX)-(dim X -1)*euler(dualSheaf)+euler(dualSheaf^**2)
     );
);



-- computes the topological euler number

eulerNumber = method();
eulerNumber (Ideal) := (X) ->
(
    if dim X != 3 then error "expected surface";
    12*(1 - irregularity(X) + geoGenus(X)) - intersectionNumber(X)
);



-- returns the basic invariants of X

invariants = method();
invariants (Ideal) := (X) ->
(
    if dim X != 3 then error "expected surface";
    R := ring X;
    q := irregularity(X);
    g := geoGenus X;
    k := intersectionNumber X;
    p := secGenus X;
    e := eulerNumber X;
    print("Genus = "|toString(g));
    print ("Irregularity = "|toString(q));	
    print("KK^2 = "|toString(k));
    print("Sectional genus = "|toString(p));
    print("Topological euler number = "|toString(e));
    return (g,q,k,p,e); 
);










-----------------------------------------------------
----- PART 2: COMPUTATION OF THE ADJUNCTION MAP -----
-----------------------------------------------------



-- computes the map given by |K_X + H|

adjunctionMap = method();
adjunctionMap (Ideal) := X ->
(
    R := ring X;
    RX := R/X;
    HX0 := X + (ideal random(1,R));
    HX0 = sub(HX0,RX);
    KX := canonicalDivisor(RX, IsGraded=>true);
    HX := divisor(HX0);	 
    Div := HX+KX;
    mapToProjectiveSpace(Div)
);



-- computes the dimension of the ambient projective space of the image under the adjunction map

dimensionOfTargetSpace = method();
dimensionOfTargetSpace (Ideal) := (X) ->
(
    if pdim (betti res X) == 2 then(
    S := ring X;
    resX := res X;
    dualresX := Hom(resX, S^{-4})[-2];
    (F0,F1,F2) := (dualresX_0, dualresX_1, dualresX_2);
    return (rank source basis(0,F0) - rank source basis(0,F1) + rank source basis(0,F2))-1
    );
    (dim source adjunctionMap X) - 1
);



-- computes the image under the adjunction map

imageUnderAdjunctionMap = method();
imageUnderAdjunctionMap (Ideal) := X ->
(
    phi := adjunctionMap X;
    trim kernel phi
);



-- computes the exceptional locus of the adjunction map

exceptLocus = method();
exceptLocus (Ideal) := (X) ->
(
    if dim X != 3 then error "expected surface";
    R := ring X;
    RX := R/X;
    H1 := sub(ideal(random(1,R))+X,RX);
    H2 := sub(ideal(random(1,R))+X,RX);
    H3 := sub(ideal(random(1,R))+X,RX);
    assert (dim (H1+H2+H3) == 0);
    phi := adjunctionMap X;
    X' := trim kernel phi;
    RX' := ring(X')/X';
    if not isBirational(map(RX,RX',phi.matrix)) then error "adjunction map is not birational";
    G1 := preimage(phi, H1);
    G2 := preimage(phi, H2);
    G3 := preimage(phi, H3);
    ideal mingens (G1+G2+G3+kernel(phi))
);










--------------------------------------------------------
----- PART 3: COMPUTATION OF THE KODAIRA DIMENSION -----
--------------------------------------------------------



-- attempt to compute the Kodaira dimension using a slow method

kodairaSlow = method();
kodairaSlow (Ideal) := (X) ->
(
    R := ring X;
    RX := R/X;
    KX := canonicalDivisor (RX, IsGraded => true);
    if dim kernel mapToProjectiveSpace(KX) == 3 then return 2;
    phi4 := mapToProjectiveSpace(4*KX);
    d := dim kernel phi4;
    if d == 3 then return 2;
    if d == 2 then return 1;
    n4 := dim source phi4;
    if n4 >= 1 then return 0;
    omegaX0 := Ext^(codim X) (R^1/X, R^{-dim R});
    omegaX := sheaf omegaX0;
    n3 := rank HH^0(omegaX^**3);
    if n3 >= 1 then return 0 else return -1;
);



-- attempt to compute the Kodaira dimension using invariants (only for surfaces)

kodairaFast = method();
kodairaFast (Ideal) := (X) ->
(
    R := ring X;
    RX := R/X;
    g := geoGenus X;
    KK := intersectionNumber X;
    if (g >= 2) and (KK > 0) then return 2;
    OX0 := R^1/X;
    OX := sheaf OX0;
    omegaX0 := Ext^(codim X) (OX0, R^{-dim R});
    omegaX := sheaf omegaX0;
    P2 := rank HH^0(omegaX^**2);
    q := rank HH^1(OX);
    if (P2 == 0) and (q == 0) then return -1;
    return -42;
);



-- computes the Kodaira dimension

kodairaDimension = method();
kodairaDimension (Ideal) := (X) ->
(
    if dim X != 3 then error "expected surface";
    d0 := kodairaFast X;
    if d0 == -1 or d0 == 2 then return d0;
    kodairaSlow X
);



-- the following methods all try to compute the minimal model, depending on the Kodaira dimension of X

classifyKodairaNeg = method();
classifyKodairaNeg (Ideal) := (X) ->
(
    q := irregularity X;
    if q >= 1 then print ("The minimal model is a non-rational ruled surface")
    else print ("The minimal model is a rational surface");
);





classifyKodaira0 = method();
classifyKodaira0 (Ideal) := (X) ->
(
    KK := intersectionNumber X;
    q := irregularity X;
    g := geoGenus X;
    if (q,g) == (0,1) then if KK != 0 then print("The surface is a non minimal K3-surface") else print("The surface is a minimal K3-surface");
    if (q,g) == (2,1) then if KK != 0 then print("The surface is a non minimal abelian surface") else print("The surface is a minimal abelian surface");
    if (q,g) == (0,0) then if KK != 0 then print("The surface is a non minimal Enriques surface") else print("The surface is a minimal Enriques surface");
    if (q,g) == (1,0) then if KK != 0 then print("The surface is a non minimal bi-elliptic surface") else print("The surface is a minimal bi-elliptic surface");
);





classifyKodaira1 = method();
classifyKodaira1 (Ideal) := (X) ->
(
    S := (ring X)/X;
    phi := adjunctionMap X;
    X' := sub(trim kernel phi,source phi);
    R' := ring X';
    S' := R'/X';
    phi' := map(S,S',phi.matrix);
    if not isBirational phi' then print ("The surface = P(E), with E an indecomposable rank 2 bundle over an elliptic curve and H = 3B, where B is  a section with B^2 = 1 on the surface")
    else (
    	E := exceptLocus X;
    	if dim E == 0 then print "The surface is a proper elliptic surface containing no (-1)-lines"
	 else (
	     inpt := read "The minimal model is a proper elliptic surface. The given surface contains (-1)-lines. Do you wish to continue the computation of the minimal model? (might take a long time) y/n: ";
	     if inpt == "y" then classifyKodaira1 X';
	     )
    );
);





classifyKodaira2 = method();
classifyKodaira2 (Ideal) := (X) ->
(
    R := ring X;
    RX := R / X;
    E := exceptLocus X;
    if dim E == 0 then print "X is a surface of general type containing no (-1)-lines" 
    else (
    	inpt := read "The surface is a surface of general type containing (-1)-lines. Do you wish to continue the computation of the minimal model? (might take a long time) y/n: ";
	if inpt == "y" then classifyKodaira2 imageUnderAdjunctionMap(X);
    );
);





classifyKodairaExceptional = method();
classifyKodairaExceptional (Ideal) := (X) ->
(
    E := exceptLocus X;
    if dim E == 0 then print "Surface contains no (-1)-lines. It is either a minimal proper elliptic surface or a non minimal surface of general type";
);





classify = method();
classify (Ideal) := (X) ->
(
    if dim X != 3 then error "expected surface";
    R := ring X;
    if dim R == 5 and degree X >52 then return classifyKodaira2 X;
    k := kodairaDimension X;
    if k == -1 then return classifyKodairaNeg X;
    if k == 0 then return classifyKodaira0 X;
    if k == 1 then return classifyKodaira1 X;
    if k == 2 then return classifyKodaira2 X;
    if k == -54 then classifyKodairaExceptional X;
);










beginDocumentation()

document{
    Key => MMPSurfaces,
    Headline => "Birational classification of smooth surfaces.",
    "TODO: Put something here",
    PARA{},
    SUBSECTION "",
    UL{	TO geoGenus,
	TO secGenus,
	TO irregularity,
	TO intersectionNumber,
	TO eulerNumber,
	TO invariants,
	TO adjunctionMap,
	TO dimensionOfTargetSpace,
	TO imageUnderAdjunctionMap,
	TO exceptLocus,
	TO kodairaDimension,
	TO classify
      }
}



doc ///
    Key
        geoGenus
        (geoGenus, Ideal)    
    Headline
        Computes the geometric genus.
    Usage
        g = geoGenus(X)
    Inputs
        X: Ideal
           the ideal of a smooth variety.
    Outputs
        g: ZZ
    	   the geometric genus of the variety.
    Description
        Text
    	    The geometric genus is given as HH^0(\omega_X). If the variety X is given by maximal minors of a matrix, a faster computation method is used.
        Example
    	    kk = ZZ/nextPrime(10000);
	    S = kk[x_0 .. x_4];
	    M = random(S^{2:0}, S^{2:-1,1:-4});
	    X = minors(2, M);
	    geoGenus(X)
    SeeAlso
    	secGenus
        irregularity
    	intersectionNumber
    	eulerNumber
    	invariants
///





doc ///
    Key
        secGenus
        (secGenus, Ideal)    
    Headline
        Computes the sectional genus.
    Usage
        p = secGenus(X)
    Inputs
        X: Ideal
           the ideal of a smooth surface.
    Outputs
        p: ZZ
    	   the sectional genus of the surface.
    Description
        Text
    	    The sectional genus of a smooth surface X is the genus of a smooth hyperplane section of X. This method computes the sectional genus.
        Example
    	    kk = ZZ/nextPrime(10000);
	    S = kk[x_0 .. x_4];
	    M = random(S^{2:0}, S^{2:-1,1:-4});
	    X = minors(2, M);
	    secGenus(X)
    Caveat
    	This method works only for surfaces.
    SeeAlso
    	secGenus
        irregularity
    	intersectionNumber
    	eulerNumber
    	invariants
///





doc ///
    Key
        irregularity
    	(irregularity, Ideal)
    Headline
        Computes the irregularity.
    Usage
        q = irregularity(X)
    Inputs
        X: Ideal
       	   the ideal of a smooth variety
    Outputs
        q: ZZ
    	   the irregularity of the variety.
    Description
        Text
    	    This method computes the irregularity as HH^1(OO_X).
        Example
    	    kk = ZZ/nextPrime(10000);
	    S = kk[x_0 .. x_4];
	    M = random(S^{2:0}, S^{2:-1,1:-4});
	    X = minors(2, M);
	    irregularity(X)
    SeeAlso
        geoGenus
	secGenus
    	intersectionNumber
    	eulerNumber
    	invariants
///





doc ///
    Key
        intersectionNumber
    	(intersectionNumber, Ideal)
    Headline
        Computes the intersection number of the canonical divisor.
    Usage
        k = intersectionNumber(X)
    Inputs
        X: Ideal
       	   the ideal of a smooth variety
    Outputs
        k: ZZ
    	   the intersection number of the canonical divisor of X.
    Description
        Text
    	    If X is a d-dimensional variety, then this method computes K_X^n. If X is a surface in P^4, a faster computation via the double point formula is used.
        Example
    	    kk = ZZ/nextPrime(10000);
	    S = kk[x_0 .. x_4];
	    M = random(S^{2:0}, S^{2:-1,1:-4});
	    X = minors(2, M);
	    intersectionNumber(X)
    SeeAlso
        geoGenus
	secGenus
    	irregularity
    	eulerNumber
    	invariants
///





doc ///
    Key
        eulerNumber
        (eulerNumber, Ideal)
    Headline
        Computes the topological Euler characteristic.
    Usage
        e = eulerNumber(X)
    Inputs
        X: Ideal
    	   the ideal of a smooth surface.
    Outputs
        e: ZZ
    	   the topological Euler characteristic of X.
    Description
        Text
    	    If X is a smooth surface, this method computes its topological Euler characteristic via Noether's formula.
        Example
    	    kk = ZZ/nextPrime(10000);
	    S = kk[x_0 .. x_4];
	    M = random(S^{2:0}, S^{2:-1,1:-4});
	    X = minors(2, M);
	    eulerNumber(X)
    Caveat
        This method only works for surfaces.
    SeeAlso
        geoGenus
	secGenus
    	irregularity
    	intersectionNumber
    	invariants
///





doc ///
    Key
        invariants
    	(invariants, Ideal)
    Headline
        Computes the invariants of a surface.
    Usage
        (g,q,k,p,e) = invariants(X)
    Inputs
        X: Ideal
    	   the ideal of a smooth surface.
    Outputs
        g: ZZ
    	   the geometric genus of X.
    	q: ZZ
    	   the irregularity of X.
    	k: ZZ
    	   the intersection number of the canonical divisor of X.
    	p: ZZ
    	   the sectional genus of X.
    	e: ZZ
    	   the topological Euler characteristic of X.   
    Description
        Text
    	    If X is a smooth surface, this method computes its basic invariants. For readability, the invariants are also printed to the screen.
        Example
    	    kk = ZZ/nextPrime(10000);
	    S = kk[x_0 .. x_4];
	    M = random(S^{2:0}, S^{2:-1,1:-4});
	    X = minors(2, M);
	    (g,q,k,p,e) = invariants(X);
	    (g,q,k,p,e) == (geoGenus(X), irregularity(X), intersectionNumber(X), secGenus(X), eulerNumber(X))
    Caveat
        This method only works for surfaces.
    SeeAlso
        geoGenus
	secGenus
    	irregularity
    	intersectionNumber
    	eulerNumber
///





doc ///
    Key
        adjunctionMap
    	(adjunctionMap, Ideal)
    Headline
        Computes the adjunction map of a surface.
    Usage
        phi = adjunctionMap(X)
    Inputs
        X: Ideal
    	   the ideal of a smooth surface.
    Outputs
        phi: RingMap
             the adjunction map of X.
    Description
        Text
    	    Let X be a smooth surface, K its canonical divisor and H its hyperplane divisor. Then, the adjunction map is the map given by the linear system |K+H|.
        Example
    	    kk = ZZ/nextPrime(10000);
	    S = kk[x_0 .. x_4];
	    M = random(S^{2:0}, S^{2:-1,1:-3});
	    X = minors(2, M);
	    SX = S/X;
	    adjunctionMap(X)
    Caveat
        This method only works for surfaces.
    	This method uses the package Divisor.
    SeeAlso
        dimensionOfTargetSpace
    	imageUnderAdjunctionMap
    	exceptLocus
///





doc ///
    Key
        dimensionOfTargetSpace
    	(dimensionOfTargetSpace, Ideal)
    Headline
        Computes the dimension of the target space of the adjunction map.
    Usage
        d = dimensionOfTargetSpace(X)
    Inputs
        X: Ideal
     	   the ideal of a smooth surface.
    Outputs
        d: ZZ
    	   the dimension of the target space of the adjunction map
    Description
        Text
    	    Let X be a smooth surface. The adjunction map maps X into some projective space. This method calculates the dimension of this space.
        Example
    	    kk = ZZ/nextPrime(10000);
	    S = kk[x_0 .. x_4];
	    M = random(S^{2:0}, S^{2:-1,1:-3});
	    X = minors(2, M);
	    SX = S/X;
	    phi = adjunctionMap(X)
	    d = dimensionOfTargetSpace(X)
	    d == (dim source phi - 1)
    Caveat
        This method only works for surfaces.
    	This method uses the package Divisor.
    SeeAlso
        adjunctionMap
    	imageUnderAdjunctionMap
    	exceptLocus
///





doc ///
    Key
        imageUnderAdjunctionMap
    	(imageUnderAdjunctionMap, Ideal)
    Headline
        Computes the image of X under the adjunction map.
    Usage
        X' = imageUnderAdjunctionMap(X)
    Inputs
        X: Ideal
    	   the ideal of a smooth surface.
    Outputs
        X': Ideal
    	    the ideal corresponding to the image of X under the adjunction map.
    Description
        Text
    	    Let X be a smooth surface, K its canonical divisor and H its hyperplane divisor. Then, the adjunction map is the map given by the linear system |K+H|. This method computes the image of X under this map.
        Example
    	    kk = ZZ/nextPrime(10000);
	    S = kk[x_0 .. x_4];
	    M = random(S^{2:0}, S^{2:-1,1:-3});
	    X = minors(2, M);
	    X' = imageUnderAdjunctionMap(X)
    Caveat
        This method only works for surfaces.
    	This method uses the package Divisor.
    SeeAlso
        adjunctionMap
    	dimensionOfTargetSpace
    	exceptLocus
///





doc ///
    Key
        exceptLocus
    	(exceptLocus, Ideal)
    Headline
        Computes the exceptional locus of the adjunction map, if it is birational.
    Usage
        E = exceptLocus(X)
    Inputs
        X: Ideal
    	   the ideal of a smooth surface.
    Outputs
        E: Ideal
    	   the ideal corresponding to the exceptional locus of the adjunction map.
    Description
        Text
    	    Let X be a smooth surface. Unless X belongs to an exceptional class, the adjunctin map will be a birational map between X and its image. This method computes the exceptional locus of this map.
        Example
    	    kk = ZZ/nextPrime(10000);
	    S = kk[x_0 .. x_4];
	    M = random(S^{2:0}, S^{2:-1,1:-3});
	    X = minors(2, M);
	    E = exceptLocus(X)
	    dim E, degree E
    Caveat
        This method only works for surfaces.
    	This method uses the package Divisor.
    	This method uses the package Cremona.
    SeeAlso
        adjunctionMap
    	dimensionOfTargetSpace
    	imageUnderAdjunctionMap
///





doc ///
    Key
        kodairaDimension
    	(kodairaDimension, Ideal)
    Headline
        Computes the Kodaira dimension.
    Usage
        kappa = kodairaDimension(X)
    Inputs
        X: Ideal
    	   the ideal of a smooth surface.
    Outputs
        kappa: ZZ
    	       the Kodaira dimension of X.
    Description
        Text
    	    Let X be a smooth surface, K its canonical divisor. The Kodaira dimension is given by kappa = max \{dim image |dK|\}, d \geq 1. This method computes the Kodaira dimension.
        Example
    	    kk = ZZ/nextPrime(10000);
	    S = kk[x_0 .. x_4];
	    M = random(S^{2:0}, S^{2:-1,1:-3});
	    X = minors(2, M);
	    kappa = kodairaDimension X
    Caveat
        This method only works for surfaces.
    	This method uses the package Divisor.
    	This method uses the package Cremona.
    SeeAlso
        classify
///





doc ///
    Key
        classify
    	(classify, Ideal)
    Headline
        Identify the minimal model.
    Usage
        classify(X)
    Inputs
        X: Ideal
           the ideal of a smooth surface.
    Description
        Text
    	    Let X be a smooth surface. The method tries to identify the minimal model of X using the Kodaira classification and adjunction theory.
        Example
    	    kk = ZZ/nextPrime(10000);
	    S = kk[x_0 .. x_4];
	    M = random(S^{2:0}, S^{2:-1,1:-3});
	    X = minors(2, M);
	    classify(X)
    Caveat
        This method only works for surfaces.
    	This method uses the package Divisor.
    	This method uses the package Cremona.
    SeeAlso
        kodairaDimension
///


end

TEST ///


///