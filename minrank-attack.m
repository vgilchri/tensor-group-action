// Set up the basic parameters
// We are interested in trilinear forms F_p^N x F_p^N -> F_p^N

p:=11;
gfp:=GF(p);
N:=10;



gfpol<[AA]>:=PolynomialRing(gfp,2*N+4*N^2,"grevlex");

// This is the ring of multilinear forms, with 3N variables
FormPoly<[XYZ]>:=PolynomialRing(gfpol,3*N);

XX:=[XYZ[i]:i in [1..N]];
YY:=[XYZ[i]:i in [N+1..2*N]];
ZZ:=[XYZ[i]:i in [2*N+1..3*N]];

// A1 and A2 are inverses to each other; B1 and B2 are inverses to each other; C1 and C2 are inverses to each other;


A1:=ZeroMatrix(FormPoly,N);
index:=1;
for i:=1 to N do 
  A1[i,i]:=AA[index];
  index:=index+1;
end for;



printf "A1=%o\n", A1;

A2:=ZeroMatrix(FormPoly,N);
for i:=1 to N do 
  A2[i,i]:=AA[index];
  index:=index+1;
end for;

printf "A2=%o\n", A2;


B1:=Matrix(FormPoly,N,N,AA[2*N+1..2*N+N^2]);
printf "B1=%o\n", B1;
B2:=Matrix(FormPoly,N,N,AA[2*N+N^2+1..2*N+2*N^2]);
printf "B2=%o\n", B2;
C1:=Matrix(FormPoly,N,N,AA[2*N+2*N^2+1..2*N+3*N^2]);
printf "C1=%o\n", C1;
C2:=Matrix(FormPoly,N,N,AA[2*N+3*N^2+1..2*N+4*N^2]);
printf "C2=%o\n", C2;


// Define the actions on the testform side
Xim:=Vector(XX)*A1;
Xim:=[Xim[i]:i in [1..N]];
Yim:=Vector(YY)*B1;
Yim:=[Yim[i]:i in [1..N]];
Zim:=Vector(ZZ)*C1;
Zim:=[Zim[i]:i in [1..N]];
TransformForwardFull:=hom<FormPoly->FormPoly|Xim cat Yim cat Zim>;
Zim:=Vector(ZZ);
Zim:=[Zim[i]:i in [1..N]];
TransformForwardA:=hom<FormPoly->FormPoly|Xim cat Yim cat Zim>;
Yim:=Vector(YY);
Yim:=[Yim[i]:i in [1..N]];
TransformForwardB:=hom<FormPoly->FormPoly|Xim cat Yim cat Zim>;

// Define the actions on the resform side
Xim:=Vector(XX);
Xim:=[Xim[i]:i in [1..N]];
Yim:=Vector(YY);
Yim:=[Yim[i]:i in [1..N]];
Zim:=Vector(ZZ)*C2;
Zim:=[Zim[i]:i in [1..N]];
TransformBackwardA:=hom<FormPoly->FormPoly|Xim cat Yim cat Zim>;
Yim:=Vector(YY)*B2;
Yim:=[Yim[i]:i in [1..N]];
TransformBackwardB:=hom<FormPoly->FormPoly|Xim cat Yim cat Zim>;
Xim:=Vector(XX)*A2;
Xim:=[Xim[i]:i in [1..N]];
TransformBackwardFull:=hom<FormPoly->FormPoly|Xim cat Yim cat Zim>;

// Define a concrete transformation
while true do
  A:=Matrix(FormPoly,N,N,[Random(gfp):i in [1..N^2]]);
  B:=Matrix(FormPoly,N,N,[Random(gfp):i in [1..N^2]]);
  C:=Matrix(FormPoly,N,N,[Random(gfp):i in [1..N^2]]);
  if Determinant(A) ne 0 and Determinant(B) ne 0 and Determinant(C) ne 0 then
    break;
  end if;
end while;
Xim:=Vector(XX)*A;
Xim:=[Xim[i]:i in [1..N]];
Yim:=Vector(YY)*B;
Yim:=[Yim[i]:i in [1..N]];
Zim:=Vector(ZZ)*C;
Zim:=[Zim[i]:i in [1..N]];
Transform:=hom<FormPoly->FormPoly|Xim cat Yim cat Zim>;


// Define the basis forms
BasisForms:=[];
for i:=1 to N do
  for j:=1 to N do
    for k:=1 to N do
      Append(~BasisForms,XX[i]*YY[j]*ZZ[k]);
    end for;
  end for;
end for;

//Define the special basis form
BasisForms1:=[];
for i:=1 to N do
  for j:=1 to N do
    for k:=1 to N do
      if i eq j and i eq k then 
        Append(~BasisForms1,XX[i]*YY[j]*ZZ[k]);
      end if;
    end for;
  end for;
end for;


pointMat:=ZeroMatrix(FormPoly,N);
for i:=1 to N do
  pointMat[i,i]:=1;
end for;


pointMat2:=pointMat*A^-1;


testform:=&+[f:f in BasisForms1];
resform:=Transform(testform);



Xim:=Vector(XX)*pointMat;
Xim:=[Xim[i]:i in [1..N]];
// Yim:=Vector(YY);
Yim:=Vector(YY);
Yim:=[Yim[i]:i in [1..N]];
Zim:=Vector(ZZ);
Zim:=[Zim[i]:i in [1..N]];
TransformBasis1:=hom<FormPoly->FormPoly|Xim cat Yim cat Zim>;

Xim:=Vector(XX)*pointMat2;
Xim:=[Xim[i]:i in [1..N]];
// Yim:=Vector(YY);
Yim:=Vector(YY);
Yim:=[Yim[i]:i in [1..N]];
Zim:=Vector(ZZ);
Zim:=[Zim[i]:i in [1..N]];
TransformBasis2:=hom<FormPoly->FormPoly|Xim cat Yim cat Zim>;

form1:=TransformBasis1(testform);
form2:=TransformBasis2(resform);


tmpformA:= TransformForwardA(form1)-TransformBackwardA(form2);
tmpformB:= TransformForwardB(form1)-TransformBackwardB(form2);
tmpfullf:= TransformForwardFull(form1)-form2;
tmpfullb:= form1-TransformBackwardFull(form2);

L:=Coefficients(tmpformA) cat Coefficients(tmpformB) cat Coefficients(tmpfullf) cat Coefficients(tmpfullb);

/*
for i:=1 to N do
  for j:=1 to N do
    if i eq j then
      val:=1;
    else
      val:=0;
    end if;
    Append(~L,Coefficients(&+[A1[i,k]*A2[k,j]:k in [1..N]]-val)[1]);
    Append(~L,Coefficients(&+[A2[i,k]*A1[k,j]:k in [1..N]]-val)[1]);
  end for;
end for;
*/

for i:=1 to N do
  for j:=1 to N do
    if i eq j then
      val:=1;
    else
      val:=0;
    end if;
//    printf "i=%o, j=%o\n", i, j;
    sp:=&+[A1[i,k]*A2[k,j]:k in [1..N]];
    if sp eq 0 then
      break;
    else 
      Append(~L,Coefficients(&+[A1[i,k]*A2[k,j]:k in [1..N]]-val)[1]);
      Append(~L,Coefficients(&+[A2[i,k]*A1[k,j]:k in [1..N]]-val)[1]);
    end if;
  end for;
end for;


for i:=1 to N do
  for j:=1 to N do
    if i eq j then
      val:=1;
    else
      val:=0;
    end if;
	Append(~L,Coefficients(&+[B1[i,k]*B2[k,j]:k in [1..N]]-val)[1]);
	Append(~L,Coefficients(&+[B2[i,k]*B1[k,j]:k in [1..N]]-val)[1]);
  end for;
end for; 

for i:=1 to N do
  for j:=1 to N do
    if i eq j then
      val:=1;
    else
      val:=0;
    end if;
	Append(~L,Coefficients(&+[C1[i,k]*C2[k,j]:k in [1..N]]-val)[1]);
	Append(~L,Coefficients(&+[C2[i,k]*C1[k,j]:k in [1..N]]-val)[1]);
  end for;
end for; 




SetVerbose("Groebner",2);
time GB:=GroebnerBasis(L);
