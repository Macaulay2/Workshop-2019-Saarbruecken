newPackage(
    "Hadmard",
    Version => "0.1",
    Date => "September 2019",
    Authors => {

	{Name => "Iman Bahmani Jafarloo",
	    Email => "ibahmani@unito.it",
	    HomePage => "http://calvino.polito.it/~imanbj"
	    }
	}, -- TODO
    Headline => "A package on Hadamard product of varieties",
    AuxiliaryFiles => false,
    DebuggingMode => true,
    Reload => true,
    PackageImports => {"Points"}
    
    )
export {
    -- types
    
    -- methods
    "hadProdOfVariet",
    "point",
    "hadProdPoints",
    "hadProdSetsOfPoints",
    "hadPowers",
    "hadMult",
    "minkowskiSum",
    "makeListOfPoints"
    -- symbols
    " "
    }
restart


--defining a new type of objects: points
Point = new Type of BasicList
point=method()
point(VisibleList):=(P)->(new Point from P)
--example--
point{1,3,5}


makeListOfPoints=method()
makeListOfPoints:=(L)->(
             apply(L,P-> point P))
	 
-----example----
makeListOfPoints(entries random(ZZ^4,ZZ^3))
---Hadamard product of two points---

hadProdPoints = method()	 
hadProdPoints(Point,Point):=(p,q)->(
    apply(p,q,times))
---example----
q=point{1,2,3}
p=point{1,3,2}
hadProdPoints(p,q)

-----group action----
Point * Point:=(p,q)->(
    apply(p,q,times)
    )

Point + Point:=(p,q)->(
    apply(p,q,plus)
    )

- Point:=(q)->(
    point apply(toList q,minus)
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

-----group action----

--S=QQ[x,y,z,w]
-- Hadamrd product of two varieties
hadProdOfVariety = method();
hadProdOfVariety (Ideal, Ideal):= (I,J) -> (
    newy := symbol newy;
    newz := symbol newz;
    varI:= gens ring I;
    varJ:= gens ring J;
    CRI:=coefficientRing ring I;
    CRJ:=coefficientRing ring J;
    RYI:=CRI[newy_0.. newy_(# varI -1)];
    RZJ:=CRI[newz_0..newz_(# varJ -1)];
    IY=sub(I,apply(varI,gens RYI,(a,b)->a=>b));
    JZ=sub(J,apply(varJ,gens RZJ,(a,b)->a=>b));
    TensorRingIJ=RYI/IY ** RZJ/JZ;
    Projvars:=apply(# gens S,i->newy_i * newz_i);
    hadMap:=map(TensorRingIJ,S, Projvars);
    ker hadMap)
------example------------
I=ideal(x,y,z^2+w^2)
J=ideal(w^2+x^2,z)
hadProdOfVariety(I,J)
---------- Minkowski sum of two varieties---------
minkowskiSum = method();
minkowskiSum(Ideal, Ideal):= (I,J) -> (
    newy := symbol newy;
    newz := symbol newz;
    varI:= gens ring I;
    varJ:= gens ring J;
    CRI:=coefficientRing ring I;
    CRJ:=coefficientRing ring J;
    RYI:=CRI[newy_0.. newy_(# varI -1)];
    RZJ:=CRI[newz_0..newz_(# varJ -1)];
    IY=sub(I,apply(varI,gens RYI,(a,b)->a=>b));
    JZ=sub(J,apply(varJ,gens RZJ,(a,b)->a=>b));
    TensorRingIJ=RYI/IY ** RZJ/JZ;
    Minkvars:=apply(#gens S,i-> -newy_i - newz_i);
    MinkMap:=map(TensorRingIJ,S,Minkvars);
    ker MinkMap)

----------example--------
I=ideal(x,y,z^2+w^2)
J=ideal(w^2+x^2,z)
minkowskiSum(I,J)

restart

--examples ----

 

-------Hadmard product of two subsets of points on two varieties---------
hadProdSetsOfPoints = method();
hadProdSetsOfPoints(List,List) :=(X,Y)->(
     convert:= obj -> if not instance(obj, Point) then point(obj) else obj;
     newX:=apply(X,convert);
     newY:=apply(Y,convert); 
     flatten apply(newX,a->apply(newY,b->a*b))
    )
---example ----
M={{1,3,6},{4,5,6}}
N={{1,0,1},{0,1,1}}
hadProdSetsOfPoints(M,N)


---Hadamard product of matrices---
pointsToMatrix = PTM -> matrix apply(PTM, toList)
hadProdMatrix=method();
hadProdMatrix(Matrix,Matrix):=(M,N)->(
    if (numrows M,numcols M) != (numrows N,numcols N) then (
	return "error: two matrices should be of the same sizes");
    rowM=makeListOfPoints entries M;
    rowN=makeListOfPoints entries N;
    pointsToMatrix(apply(rowM,rowN,(i,j)->hadProdPoints(i,j)))
    )

--example---
M=random(ZZ^4,ZZ^4)
N=random(QQ^4,QQ^4)
loadPackage "Points"
M=transpose randomPointsMat(R,4)
N=transpose randomPointsMat(R,4)
hadProdMatrix(M,N)

-----------------------------$$$$$------------

---Hadamard powers of varieties------------
hadPowers = method();
hadPowers(Ideal,ZZ):=(I,r)->(
   NewI = I;
   for i from 1 to r-1 do NewI = hadProdOfVariety(NewI,I);
   return NewI)

----example--
I=ideal(random(1,S),random(1,S),random(1,S))
hadPowers(I,3)
---Hadamard powers of Matrix------------
hadPowers(Matrix,ZZ):=(M,r)->(
   NewM = M;
   for i from 1 to r-1 do NewM = hadProdMatrix(NewM,M);
   return NewM)

--example---
M=random(ZZ^4,ZZ^4)
hadPowers(M,2)
---Hadamard powers of sets of points ------------

hadPowers(List,ZZ):=(L,r)->(
   NewL = L;
   for i from 1 to r-1 do NewL = hadProdSetsOfPoints(NewL,L);
   return NewL)

---example---
Y={{1,0,1},{0,1,1}}
hadPowers(Y,2)
-----
----Hadamard product of set of the same Type elements in side a list--
-----------------%%%---------------
hadMultVars:=(L)->(fold(hadProdOfVariety,L))
-----------------%%%--------------------------------%%%---------------
hadMultListInList:=(L)->(
convert:= obj -> if not instance(obj, Point) then point(obj) else obj;
	newL:=apply(L,convert);
	  fold(hadProdPoints,newL))
-----------------%%%--------------------------------%%%---------------
hadMultPointsInList:=(L)->(fold(hadProdPoints,L))
-----------------%%%--------------------------------%%%---------------
hadMultMatsInList:=(L)->(fold(hadProdMatrix,L))
-----------------%%%--------------------------------%%%---------------
hadMult=method();
hadMult(List):=(L)->(
    if not uniform L then
     (return "error: the elements of the list are not all of the same class");
    if instance(first L,Ideal)==true then hadMultVars(L)
    else
    if instance(first L,List)==true then hadMultListInList(L)
    else
    if  instance(first L,Point)==true then hadMultPointsInList(L)
    else 
    if instance(first L,Matrix)==true then hadMultMatsInList(L)
    else return ("error: check the inputs")
    )
-----------example-----------
hadMult({I,I,I})
hadMult({{0,4,5,6},{1,2,3,4}})
hadMult({random(ZZ^3,ZZ^4),random(ZZ^3,ZZ^4)})
hadMult({point{0,4,5,6},point{1,2,3,4}})



-----------------------new results-----------------


















restart
