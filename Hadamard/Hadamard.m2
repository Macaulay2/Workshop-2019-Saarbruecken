newPackage(
    "Hadamard",
    Version => "1.0",
    Date => "September 2019",
    Authors => {

	{Name => "Iman Bahmani Jafarloo",
	    Email => "iman.bahmanijafarloo@polito.it",
	    HomePage => "http://calvino.polito.it/~imanbj"
	    }
	}, -- TODO
    Headline => "A package for Hadamard products and Minkowski sums of varieties",
    AuxiliaryFiles => false,
    DebuggingMode => true,
    Reload => true,
    PackageExports => {"Points"}
    
    )
export {
    -- types
    
    -- methods
    "point",
    "makeListOfPoints",
    "hadamardProduct",
    "hadamardPowers",
    "hadamardMult",
    "pointsToMatrix",
    "minkSum",
    "minkSumPowers",
    "minkMult",
    "idealOfProjectivePoints",
    "inversion"
    }


--defining a new type of objects: points

Point = new Type of BasicList
point=method()
point(VisibleList):=(P)->(new Point from P)


makeListOfPoints=method()
makeListOfPoints(VisibleList):=(L)->(
             apply(L,P-> point P)
	     )

Point * Point:=(p,q)->(
    apply(p,q,times)
    )

Point + Point:=(p,q)->(
    apply(p,q,plus)
    )

- Point:=(q)->(
    point apply(toList q,minus)
    )

Point - Point :=(p,q)->(
    p+(-q)
    )

Point / Thing:=(q,t)->(
    point apply(toList q,i->i/t)
    )

Thing * Point:=(t,p)->(
    Np:=toList p;
     point( t * Np)
     )

Point * Thing :=(p,t)->(
    Np:=toList p;
     point(flatten apply(Np,i->apply({t},{i},times)))
     )

---Hadamard product of two points---


hadProdPoints = method()	 
hadProdPoints(Point,Point):=(p,q)->(
    apply(p,q,times)
    )

hadProdPoints(List,List):=(p,q)->(
    apply(point p,point q,times)
    )

hadProdPoints(Array,Array):=(p,q)->(
    apply(point p,point q,times)
    )


-- Hadamrd product of two varieties
hadProdOfVariety = method()
hadProdOfVariety (Ideal, Ideal):= (I,J) -> (
    newy := symbol newy;
    newz := symbol newz;
    varI:= gens ring I;
    varJ:= gens ring J;
    CRI:=coefficientRing ring I;
    CRJ:=coefficientRing ring J;
    RYI:=CRI[newy_0.. newy_(# varI -1)];
    RZJ:=CRI[newz_0..newz_(# varJ -1)];
    IY:=sub(I,apply(varI,gens RYI,(a,b)->a=>b));
    JZ:=sub(J,apply(varJ,gens RZJ,(a,b)->a=>b));
    TensorRingIJ:=RYI/IY ** RZJ/JZ;
    use TensorRingIJ;
    Projvars:=apply(#(gens ring I),i->newy_i * newz_i);
    hadMap:=map(TensorRingIJ,ring I, Projvars);
    ker hadMap
    )
 

-------Hadmard product of two subsets of points on two varieties---------
hadProdListsOfPoints = method()
hadProdListsOfPoints(List,List) :=(X,Y)->(
     convert:= obj -> if not instance(obj, Point) then point(obj) else obj;
     newX:=apply(X,convert);
     newY:=apply(Y,convert); 
     toList(set(flatten apply(newX,a->apply(newY,b->a*b)))-set({point flatten{apply(#first newX,i->0)}}))
     )



---Hadamard product of matrices---

pointsToMatrix=method()
pointsToMatrix(List):= (PTM) ->( matrix apply(PTM, toList))

hadamardProductMatrix=method()
hadamardProductMatrix(Matrix,Matrix):=(M,N)->(
    if (numrows M,numcols M) != (numrows N,numcols N) then (
	return "error: two matrices should be of the same sizes");
    rowM:=makeListOfPoints entries M;
    rowN:=makeListOfPoints entries N;
    pointsToMatrix(apply(rowM,rowN,(i,j)->hadProdPoints(i,j))) 
    )



---Hadamard powers of varieties------------

hadamardPowers = method()
hadamardPowers(Ideal,ZZ):=(I,r)->(
   NewI := I;
   for i from 1 to r-1 do NewI = hadProdOfVariety(NewI,I);
   return NewI)


---Hadamard powers of Matrix------------
hadamardPowers(Matrix,ZZ):=(M,r)->(
   NewM := M;
   for i from 1 to r-1 do NewM = hadamardProductMatrix(NewM,M);
   return NewM)


---Hadamard powers of sets of points ------------

hadamardPowers(List,ZZ):=(L,r)->(
   NewL := L;
   for i from 1 to r-1 do NewL = hadProdListsOfPoints(NewL,L);
   return toList set NewL)


-----------------%%%--------------------------------%%%---------------

hadamardMult=method()
hadamardMult(List):=(L)->(
    if not uniform L then
     (return "error: the elements of the list are not all of the same class");
    if instance(first L,Ideal)==true then fold(hadProdOfVariety,L)
    else
    if instance(first L,List)==true or instance(first L,Point)==true then fold(hadProdPoints,L)
    else
    if instance(first L,Matrix)==true then fold(hadamardProductMatrix,L)
    else return ("error: check the inputs")
    )


-------general product------

hadamardProduct=method()
hadamardProduct(Ideal,Ideal):=(I,J)->(hadProdOfVariety(I,J))
hadamardProduct(List,List):=(X,Y)->(hadProdListsOfPoints(X,Y))
hadamardProduct(Matrix,Matrix):=(M,N)->(hadamardProductMatrix(M,N))




------------------Hadamard product ends ------------------


---------- Minkowski sum of two varieties starts---------

minkowskiSumOfVariety = method()
minkowskiSumOfVariety(Ideal, Ideal):= (I,J) -> (
    newy := symbol newy;
    newz := symbol newz;
    varI:= gens ring I;
    varJ:= gens ring J;
    CRI:=coefficientRing ring I;
    CRJ:=coefficientRing ring J;
    RYI:=CRI[newy_0.. newy_(# varI -1)];
    RZJ:=CRI[newz_0..newz_(# varJ -1)];
    IY:=sub(I,apply(varI,gens RYI,(a,b)->a=>b));
    JZ:=sub(J,apply(varJ,gens RZJ,(a,b)->a=>b));
    TensorRingIJ:=RYI/IY ** RZJ/JZ;
    use TensorRingIJ;
    Minkvars:=apply(#gens ring I,i-> newy_i + newz_i);
    MinkMap:=map(TensorRingIJ,ring I,Minkvars);
    ker MinkMap
    )


minkSumPoints = method()     
minkSumPoints(Point,Point):=(p,q)->(p + q)
minkSumPoints(List,List):=(p,q)->(point p + point q)
minkSumPoints(Array,Array):=(p,q)->(point p + point q)


minkSumListsOfPoints = method();
minkSumListsOfPoints(List,List) :=(X,Y)->(
     convert:= obj -> if not instance(obj, Point) then point(obj) else obj;
     newX:=apply(X,convert);
     newY:=apply(Y,convert); 
     toList set flatten apply(newX,a->apply(newY,b->a+b))
     )


---Mink powers of varieties------------
minkSumPowers = method()
minkSumPowers(Ideal,ZZ):=(I,r)->(
   NewI := I; 
   for i from 1 to r-1 do NewI = minkowskiSumOfVariety(NewI,I);
   return NewI
   )


---Hadamard powers of list of points ------------

minkSumPowers(List,ZZ):=(L,r)->(
   NewL := L;
   for i from 1 to r-1 do NewL = minkSumListsOfPoints(NewL,L);
   return toList set NewL
   )

---Hadamard powers of a matrix ------------

minkSumPowers(Matrix,ZZ):=(M,r)->(
   NewM := M;
   for i from 1 to r-1 do NewM = M + NewM;
   return NewM
   )


minkSum=method()
minkSum(Ideal,Ideal):=(I,J)->(minkowskiSumOfVariety(I,J))
minkSum(List,List):=(X,Y)->(minkSumListsOfPoints(X,Y))
minkSum(Matrix,Matrix):=(M,N)->(M+N)


-----------------%%%--------------------------------%%%---------------

minkMult=method()
minkMult(List):=(L)->(
    if not uniform L then
     (return "error: the elements of the list are not all of the same class");
    if instance(first L,Ideal)==true then fold(minkowskiSumOfVariety,L)
    else
    if instance(first L,List)==true or instance(first L,Point)==true or instance(first L,Array)==true
    then fold(minkSumPoints,L)
    else
    if instance(first L,Matrix)==true then sum L
    else return ("error: check the inputs")
    )

-------------minkowskiSum--ends-------

-----------------------new results-------------
idealOfProjectivePoints=method()
idealOfProjectivePoints(List,Ring):=(L,R)->(
    if not uniform L then 
     (return "error: the elements of the list are not all of the same class");
    if instance(first L,Point)==true then(
    MP:=transpose pointsToMatrix L; 
    ideal projectivePointsByIntersection(MP,R)
    )
    else
    if instance(first L,Array)==true then(
    newL:=makeListOfPoints(L);
    MA:=transpose pointsToMatrix newL;
    ideal projectivePointsByIntersection(MA,R)
    )
    else
    if instance(first L,List)==true then(
    ML:=transpose matrix L;
    ideal projectivePointsByIntersection(ML,R)
    )
    else return ("error: check the inputs")
    )


-----------------------%%inversion%%---------------
inversion = method()
inversion(Point):=(P)->(
    newP := toList P;
    if #delete(0,newP) =!= # newP then 
      (return "error: there exists at least one zeor in the coordinate");
      point apply(newP,i->1/i)
      )
inversion(List):=(P)->(
    if #delete(0,P) =!= # P then 
      (return "error: there exists at least one zeor in the coordinate");
      apply(P,i->1/i)
      )
inversion(Array):=(P)->(
    if #delete(0,P) =!= # P then 
      (return "error: there exists at least one zeor in the coordinate");
      new Array from apply(P,i->1/i)
      )
inversion(RingElement):=(L)->(
    newC := flatten entries(coefficients L)#1;
    if #delete(0,newC) =!= # newC then 
      (return "error: there exists at least one zeor in the coordinate");
      sub(sum apply(gens ring L, apply(newC,i->1/i),(a,b)->a*b),ring L)
      )



-----------------------------------------------
beginDocumentation()

     doc ///
       Key 
        Hadamard
     Headline
      A package for Hadamard products and Minkowski sums of varieties
     Description
       Text
        This package computes the Hadamard products and Minkowski sums of varieties.
     ///


doc ///
    Key
     point
    Headline
        consructs points from a list or an array.
    Usage
        point(List)
        point(Array)
    Inputs
        p:List
        p:Array 
    Outputs
        :Point
    Description
        Text
          This function makes a point from a list or an array
        Example
            p = {1,2,3} 
            point(p)
            q = [1,2,3]
            point(q)
///


doc ///
    Key
     makeListOfPoints
    Headline
        consructs a list of points from a list of lists or arraies.
    Usage
        makeListOfPoints(List)
    Inputs
        L:List
    Outputs
         :List
    Description
        Text
          consructs a list of points from a list of lists or arraies.
        Example
            L = {{1,2,3},{4,5,6},{7,8,9}}
            makeListOfPoints(L)
            L = {[1,2,3],[4,5,6],[7,8,9]} 
            makeListOfPoints(L)
///

doc ///
    Key
     hadamardProduct
    Headline
        Hadamard products of varieties, subsets of points and matrices.    
    Usage
        hadamardProduct(Ideal,Ideal)
        hadamardProduct(List,List)
        hadamardProduct(Matrix,Matrix)
    Inputs
        I:Ideal
        J:Ideal
        K:List
        L:List
        M:Matrix
        N:Matrix
    Outputs
         :Ideal
         :List
         :Matrix
    Description
        Text
          Hadamard products of varieties, subsets of points and matrices.
        Example
            S = QQ[x,y,z,w]
            I = ideal(random(1,S),random(1,S))
            J = ideal(random(1,S),random(1,S))
            hadamardProduct(I,J)
            K = {{1,2,3,4},{1,1,3,4},{2,5,6,0},{1,2,0,0}}
            L = {{1,2,3,4},{1,1,3,4},{1,1,1,1}}
            hadamardProduct(K,L)
            M = matrix{{1,2,3,4},{1,1,3,4},{2,5,6,0},{1,2,0,0}}
            N = matrix{{1,2,3,4},{1,1,3,4},{1,1,1,1},{1,2,3,4}}
            hadamardProduct(M,N)
///

doc ///
    Key
     hadamardPowers
    Headline
        computes the r-th Hadmard powers of varieties, subsets of points, and matrices.
    Usage
        hadamardPowers(Ideal,ZZ)
        hadamardPowers(List,ZZ)
        hadamardPowers(Matrix,ZZ)
    Inputs
        r:ZZ
        I:Ideal
        L:List
        M:Matrix
    Outputs
         :Ideal
         :List
         :Matrix
    Description
        Text
         computes the r-th Hadmard powers of varieties, subsets of points, or matrices.
        Example
            S=QQ[x,y,z,w]
            I=ideal(random(1,S),random(1,S),random(1,S))
            hadamardPowers(I,3)
            M=random(ZZ^4,ZZ^4)
            hadamardPowers(M,2)
            L={point{1,1,1},point{1,0,1},point{1,2,4}}
            hadamardPowers(L,3)
///

doc ///
    Key
     hadamardMult
    Headline
        it computes pairwise Hadmard products of the elements in a list of ideals, matrices, or points.
    Usage
        hadamardMult(List)
    Inputs
        L:List
    Outputs
         :Ideal
         :Point
         :Matrix
    Description
        Text
         it computes pairwise Hadmard products of the elements in a list of ideals, matrices, or points.
        Example
            S=QQ[x,y,z,w]
            L={ideal(random(1,S),random(1,S)),ideal(random(1,S),random(1,S)),ideal(random(1,S),random(1,S),random(1,S))}
            hadamardMult(L)
            L={point{0,4,5,6},point{1,2,3,4},point{1,2,0,1}}
            hadamardMult(L)
            L={random(ZZ^3,ZZ^4),random(ZZ^3,ZZ^4),random(ZZ^3,ZZ^4)}
            hadamardMult(L)
///

doc ///
    Key
     pointsToMatrix
    Headline
        consructs a matrix from a list of points.
    Usage
        pointsToMatrix(List)
    Inputs
        L:List
    Outputs
         :Matrix
    Description
        Text
          consructs a matrix from a list of points.
        Example
            L = {point{1,2,3},point{4,5,6},point{7,8,9}}
            pointsToMatrix(L)
///

doc ///
    Key
     minkSum
    Headline
        Minkowski sums of varieties, subsets of points and matrices.    
    Usage
        minkSum(Ideal,Ideal)
        minkSum(List,List)
        minkSum(Matrix,Matrix)
    Inputs
        I:Ideal
        J:Ideal
        K:List
        L:List
        M:Matrix
        N:Matrix
    Outputs
         :Ideal
         :List
         :Matrix
    Description
        Text
          Minkowski sums of varieties, subsets of points and matrices.
        Example
            S = QQ[x,y,z,w]
            I = ideal(random(1,S),random(1,S),random(1,S))
            J = ideal(random(1,S),random(1,S),random(1,S))
            minkSum(I,J)
            K = {point{1,2,3,4},point{1,1,3,4},point{2,5,6,0},point{1,2,0,0}}
            L = {point{1,2,3,4},point{1,1,3,4},point{1,1,1,1}}
            minkSum(K,L)
            M = matrix{{1,2,3,4},{1,1,3,4},{2,5,6,0},{1,2,0,0}}
            N = matrix{{1,2,3,4},{1,1,3,4},{1,1,1,1},{1,2,3,4}}
            minkSum(M,N)
///

doc ///
    Key
     minkSumPowers
    Headline
        computes the r-th Minkowski sums of varieties, subsets of points, and matrices.
    Usage
        minkSumPowers(Ideal,ZZ)
        minkSumPowers(List,ZZ)
        minkSumPowers(Matrix,ZZ)
    Inputs
        r:ZZ
        I:Ideal
        L:List
        M:Matrix
    Outputs
         :Ideal
         :List
         :Matrix
    Description
        Text
         computes the r-th Minkowski sums of varieties, subsets of points, or matrices.
        Example
            S=QQ[x,y,z,w]
            I=ideal(random(1,S),random(1,S),random(1,S))
            minkSumPowers(I,3)
            M=random(ZZ^4,ZZ^4)
            minkSumPowers(M,2)
            L={point{1,1,1},point{1,0,1},point{1,2,4}}
            minkSumPowers(L,3)
///

doc ///
    Key
     minkMult
    Headline
        it computes pairwise Minkowski sums of the elements in a list of ideals, matrices, or points.
    Usage
        minkMult(List)
    Inputs
        L:List
    Outputs
         :Ideal
         :Point
         :Matrix
    Description
        Text
         it computes pairwise Minkowski sums of the elements in a list of ideals, matrices, or points.
        Example
            S = QQ[x,y,z]
            I = ideal(x-y,x-z)
            L = {I,I}
            minkMult(L)
            L = {point{0,4,5,6},point{1,2,3,4},point{1,2,0,1}}
            minkMult(L)
            L = {random(ZZ^3,ZZ^4),random(ZZ^3,ZZ^4),random(ZZ^3,ZZ^4)}
            minkMult(L)
///


doc ///
    Key
     idealOfProjectivePoints
    Headline
        ideal associated to a list of points, lists, or arraies.
    Usage
        idealOfProjectivePoints(List)
    Inputs
        L:List
    Outputs
        I:Ideal
    Description
        Text
          ideal associated to a list of points, lists, or arraies.
        Example
            S = QQ[x,y,z] 
            L = {point{1,1,0},point{0,1,1},point{1,2,-1}}
            I = idealOfProjectivePoints(L,S)
            L = {{1,1,0},{0,1,1},{1,2,-1}}
            I = idealOfProjectivePoints(L,S)
            L = {[1,1,0],[0,1,1],[1,2,-1]}
            I = idealOfProjectivePoints(L,S)
            I2 = hadamardPowers(I,2)
            L2 = hadamardPowers(L,2)
            I2 == idealOfProjectivePoints(L2,S)
///

doc ///
    Key
     inversion
    Headline
        coordinate wise inversion of a point, list, or array.
    Usage
        inversion(Point)
        inversion(List)
        inversion(Array)
    Inputs
        P:Point
        P:List
        P:Array
        L:RingElement
    Outputs
         :Point
         :List
         :Array
         :RingElement
    Description
        Text
          ccoordinate wise inversion of a point, a list, an array, or a linear form.
        Example
            P = point{1,2,3}
            inversion(P)
            P = {1,2,3}
            inversion(P)
            P = [1,2,3]
            inversion(P)
            S = QQ[x,y,z,w]
            L=random(1,S)
            inversion(L)

///

     TEST ///
     assert(hadamardProduct({point{1,2,3,4}},{point{1,2,3,4}}))==point{1,4,9,16})
 
     -- may have as many TEST sections as needed
     ///

end


restart
uninstallPackage "Hadamard"
installPackage "Hadamard"
loadPackage "Hadamard"
viewHelp Hadamard









