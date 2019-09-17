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
    "makePoint",
    "hadProdPoints",
    "hadProdSetOfPoints",
    "hadPowers",
    -- symbols
    "dims"
    }
restart
S=QQ[x,y,t,w]
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
    Projvars:=apply(# gens S,i->newy_i* newz_i);
    hadMap:=map(TensorRingIJ,S, Projvars);
    ker hadMap)

--example ----
I=ideal(random(1,S),random(1,S),random(1,S))
J=ideal(random(1,S),random(1,S),random(1,S))

hadProdOfVariety(I,J)
restart
--defining a new type of objects: points
Point = new Type of BasicList
point=method()
point(VisibleList):=(P)->(new Point from P)
--example--
point{1,3,5}
point (1,3,4)


--makePoints=method()
makePoints:=(L)->(
             apply(L,P-> point P)
	     )
---Hadamard product of two points---
hadProdPoints = method()	 
hadProdPoints(Point,Point):=(p,q)->(
    apply(p,q,times)
    )

Point * Point:=(p,q)->(
    apply(p,q,times)
    )

Point + Point:=(p,q)->(
    apply(p,q,plus)
    )
p+q

Thing * Point:=(t,p)->(
    Np:=toList p;
     point( t * Np)
     )
fold(hadProdPoints,{p,q,q})
 
---example----
q=point{1,2,3}
p=point{1,3,2}
hadProdPoints(p,q)

--Hadmard product of two subsets of points on two varieties

X={{2,3,4},{1,2,3},p,q,(1,2,3)}
hadProdSetOfPoints = method();
hadProdSetOfPoints(List,List) :=(X,Y)->(
     convert:= obj -> if not instance(obj, Point) then point(obj) else obj;
     X=apply(X,convert);
     Y=apply(Y,convert) ; 
     apply(newX,a->apply(newY,b->hadProdPoints(a,b)))
    )
---example ----
X={{1,3,6},{4,5,6}}
Y={{1,0,1},{0,1,1}}
hadProdSetOfPoints(M,N)



---Hadamard product of matrices---
pointsToMatrix = PTM -> matrix apply(PTM, toList)
hadProdMatrix=method();
hadProdMatrix(Matrix,Matrix):=(M,N)->(
    if (numrows M,numcols M) != (numrows N,numcols N) then (
	return "error: two matrices should be of the same sizes");
    rowM=makePoints entries M;
    rowN=makePoints entries N;
    pointsToMatrix(apply(rowM,rowN,(i,j)->hadProdPoints(i,j)))
    )

--example---
M=random(ZZ^2,ZZ^2)
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

---Hadamard powers of Matrix------------
hadPowers(Matrix,ZZ):=(M,r)->(
   NewM = M;
   for i from 1 to r-1 do NewM = hadProdMatrix(NewM,M);
   return NewM)

--example---
hadPowers(M,2)
---Hadamard powers of sets of points ------------
hadPowers(List,ZZ):=(L,r)->(
   NewL = L;
   for i from 1 to r-1 do NewL = hadProdSetOfPoints(NewL,L);
   return NewL)



select(U, List)




--example ---
I=(random(1,S),random(1,S),random(1,S))
Object=I
hadPowers(I,3)
----










