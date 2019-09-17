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
    Reload => true
    )
export {
    -- types
    
    -- methods
    "hadProdOfVariet",
    "hadProdOfPoints"
    ,
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


--Hadmard product of two subset of points on a varieties
hadProdOfPoints = method();
hadProdOfPoints(VisibleList,VisibleList) :=(X,Y)->(    
   toList set flatten apply(X,a->apply(Y,b->apply(a,b,(i,j)->i*j)))
    )

hadProdOfPoints(X,Y)

---example ----
M={{1,3,6}}
N={{1,0,1},{0,1,1}}
hadProdOfPoints(M,N)

---Hadamard power
hadPower = method();
hadPower:=(I,r)->(    
   NewI = I;
   for i from 1 to r-1 do NewI = hadProdOfVariety(NewI,I);
   return NewI
    )

--example ---
I=ideal(random(1,S),random(1,S),random(1,S))
hadPower(I,3)

----










