newPackage(
    "Hadamard",
    Version => "1.0",
    Date => "September 2019",
    Authors => {

	{Name => "Iman Bahmani Jafarloo",
	    Email => "ibahmani@unito.it",
	    HomePage => "http://calvino.polito.it/~imanbj"
	    }
	}, -- TODO
    Headline => "A package for Hadamard product and Minkowski sums of varieties",
    AuxiliaryFiles => false,
    DebuggingMode => true,
    Reload => true,
    PackageImports => {"Points"},
    PackageExports => {"Points"}
    
    )
export {
    -- types
    
    -- methods
    "point",
    "makeListOfPoints",
    "pointsToMatrix",
    "hadamardPowers",
    "hadamardMult",
    "hadamardProduct",
    "minkSumPowers",
    "minkSum",
    "minkMult",
    "idealOfProjectivePoints"
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




beginDocumentation()

     doc ///
       Key 
        Hadamard
     Headline
      A package for Hadamard product and Minkowski sums of varieties
     Description
       Text
        We know what we are doing here!
       Example
        hadamardProduct({point{1,2,3,4}},{point{1,2,3,4}})
     SeeAlso
      
     ///


     TEST ///
     assert(hadamardProduct({point{1,2,3,4}},{point{1,2,3,4}}))==point{1,4,9,16})
 
     -- may have as many TEST sections as needed
     ///
  
     
end





















