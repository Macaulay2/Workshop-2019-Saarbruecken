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

--defining a new type of objects: points
Point = new Type of BasicList
makePoint=method()
makePoint(List):=(P)->(new Point from P)

--example--
makePoint {1,3,5}

--makePoints=method()
makePoints:=(L)->(
             apply(L,P-> makePoint P)
	     )
---Hadamard product of two points---
hadProdPoints = method()	 
hadProdPoints(Point,Point):=(p,q)->(
    apply(p,q,times)
    )

---example----
q=makePoint{1,2,3}
p=makePoint{1,3,2}
hadProdPoints(p,q)


--Hadmard product of two subsets of points on two varieties
hadProdSetOfPoints = method();
hadProdSetOfPoints(VisibleList,VisibleList) :=(X,Y)->(
     newX:= makePoints X ;
     newY:= makePoints Y;
   apply(newX,a->apply(newY,b->hadProdPoints(a,b)))
    )

---example ----
M={{1,3,6}}
N={{1,0,1},{0,1,1}}
hadProdSetOfPoints(M,N)

---Hadamard powers
hadPowers = method();
hadPowers(Ideal,ZZ):=(I,r)->(    
   NewI = I;
   for i from 1 to r-1 do NewI = hadProdOfVariety(NewI,I);
   return NewI
    )

--example ---
I=ideal(random(1,S),random(1,S),random(1,S))
hadPowers(I,3)
----

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
M=random(QQ^4,QQ^4)
N=random(QQ^4,QQ^4)
loadPackage "Points"
M=transpose randomPointsMat(R,4)
N=transpose randomPointsMat(R,4)
hadProdMatrix(M,N)








