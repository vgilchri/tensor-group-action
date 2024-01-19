//set up base parameters
n := 30;
q := 2039;
F := FiniteField(q);


identity := function(k,FF)
// makes k x k identity matrix
	basis := []; // compute basis vectors
	for i in [1..k] do 
		e := [FF!0 : j in [1..k]];
		e[i] := FF!1;
		basis := basis cat e;
	end for;
	M := Matrix(k,basis);
	return M;
end function;

IsInvertible := function(M) // checks if M is invertible
	Z := Parent(M[1][1]);
	if Z!Determinant(M) eq 0 then 
		return false;
	end if;
	return true;
end function;

InvMatrix := function(n) // computes a random invertible matrix
	A := Matrix(n,n,[Random(F):i in [1..n^2]]);
	while IsInvertible(A) eq false do 
		A := Matrix(n,n,[Random(F):i in [1..n^2]]);
	end while;
	return A;
end function;

keygen := function()
// chooses random secret key values, and computes the corresponding public key
	b := Random([0,1]); 
	A := InvMatrix(n);
	B := InvMatrix(n);
	C := InvMatrix(n);
	//pk := GACE(A,B,C,b);
	return A,B,C,b; //,pk;
end function;

// Implemented our own tensor product : a list of matrices
tensor_prod := function(u,v,w)
// return the tensor product of u,v,w of dim n as an n x n x n array 
//assume the input vectors are array of coefficients with respect to the canonical basis of F_q^n
	tsr := Matrix(F,n,1,v)*Transpose(Matrix(F,n,1,w)); //tested and works 
	lst:=[* *];
	for i in [1..n] do
		//"u[i]:";
		//u[i];
		//"tsr:";
		//tsr;
		mat:=ScalarMatrix(F,n,u[i]);
		el:= [* mat*tsr *]; // u_i multiplies each element of tsr
		//"element is:";
		//el;
		lst := lst cat el;
	end for;
	//"final tensor product";
	//lst;
	return lst; 
end function;

// used to compute public key given a secret key
Commitment := function(A,B,C,b)
	//basis:=identity(n,P);
	sum:=0;
    lst:=[**]; // empty list 
	for i in [1..n] do
	//ei := Matrix(n,1,basis[i]);
        mat:=identity(n,Parent(A[1][1]));
        for j in [1..n] do
        //ej := Matrix(n,1,basis[j]);
            for k in [1..n] do
                sum:=0;
                for s in [1..(n-b)] do //changing order of the s sum doesn't change input 
                    //ek := Matrix(n,1,basis[k]);
                    coeff:=A[i][s]*B[j][s]*C[k][s];
                    //"Coeff";
                    //coeff;
                    sum:=sum+coeff;
                end for;
                mat[j][k]:=sum;
                //"Current matrix";
                //mat;
                //at the end of this loop sum is the coeff at the i,j,k spot of the nxnxn array
            end for;
        end for;
        el:=[*mat*];
        //"matrix in a list";
       // el;
        lst:=lst cat el;
        //"list";
        //lst;
	end for;
	return lst; // returns a n list of nxn matrices representing the output of the action 
end function;

// ---------------------- rank 0 attack with built-in magma fn ----------------------------------------------------------------------
RankAttack := function(pk,n)
	poly<[AA]> := PolynomialRing(F, n); // define variables to be solved
	M := ZeroMatrix(F,n); // initialize matrix to store equations
	for i in [1..n] do 
		M := M + AA[i]*pk[i]; // compute set of equations: a1 G1 + ... an Gn
	end for;
	K := Kernel(M); // compute kernel of above matrix
	dim := #(Basis(K)); // count number of solutions
	if dim eq 0 then // if no solutions, then pk had rank n so b=0
		return 0;
	end if;
	return 1; // if there are solutions, pk had rank n-1 so b=1
end function;

// ---------------------- rank 0 attack that finds solutions ------------------
RankAttack2 := function(pk)
	poly<[AA]> := PolynomialRing(F, n); // define variables to be solved
	M := ZeroMatrix(F,n); // initialize matrix to store equations
	for i in [1..n] do 
		M := M + AA[i]*pk[i]; // compute set of equations: a1 G1 + ... an Gn
	end for;
	eqns := [];
	for i in [1..n] do 
		eqns := eqns cat [M[i][j] : j in [1..n]]; // place all equations into list
	end for;
	I := Ideal(eqns);
	K := Variety(I);
	dim := #K;
	//dim := #(Basis(K)); // count number of solutions
	if dim eq 1 then // if only zero solution, then pk had rank n so b=0
		return 0;
	end if;
	return 1; // if there are non-zero solutions, pk had rank n-1 so b=1
end function;

// A,B,C,b := keygen();
// pk := Commitment(A,B,C,b);
// time b1 := RankAttack(pk);
// time b2 := RankAttack2(pk);
// b1 eq b2;

//---------------------------------Experiments 
//set up base parameters
// n := 30;
// q := 2039;
// F := FiniteField(q);
// Repeat m times
CountFullRank:=function(m,n,q)
    count:=0; 
    for i in [1..m] do 
        t:=[**];
    //Create a random n dim 3-tensor as collection of matrices 
        for i in [1..n] do
            M:=RandomMatrix(F, n, n);
            el:=[*M*];
            t:=t cat el;
        end for;
        //run attack to check if it has rank 0 points 
        count+:=RankAttack(t,n);
        // if so add to count 
    end for;
    return count;
end function;

for n in [10..30] do
q:=2039;
F := FiniteField(q);
ctr:=CountFullRank(100,n,q);
"q,n,ctr";
q;
n;
ctr;
q:=4093;
F := FiniteField(q);
ctr:=CountFullRank(100,n,q);
"q,n,ctr";
q;
n;
ctr;
end for;

//debug by giving n as input to the rankattack function 