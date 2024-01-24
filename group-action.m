clear;

// set up base parameters
// n := 6; q := 37;
//n := 14; q := 4093;
// n := 22; q := 4093;
 n := 30; q := 2039;
F := FiniteField(q);

// gives helper functions for attacks on DTI and CTI variants

// makes k x k identity matrix over finite field FF
identity := function(k,FF)
	M := ZeroMatrix(FF,k);
	for i in [1..k] do 
		M[i][i] := FF!1;
	end for;
	return M;
end function;

// Implemented our own tensor product : a list of matrices
tensor_prod := function(u,v,w)
// return the tensor product of u,v,w of dim n as an n x n x n array 
//assume the input vectors are array of coefficients with respect to the canonical basis of F_q^n
	tsr := Matrix(F,n,1,v)*Transpose(Matrix(F,n,1,w)); //tested and works 
	lst:=[* *];
	for i in [1..n] do
		mat:=ScalarMatrix(F,n,u[i]);
		el:= [* mat*tsr *]; // u_i multiplies each element of tsr
		lst := lst cat el;
	end for;
	return lst; 
end function;

// performs the general group action (A,B,C)*X
star := function(A,B,C,X)
//Assume X is represented using our tensor product representation as above
sum:=0;
lst:=[**];
for l in [1..n] do
    mat:=identity(n,Parent(A[1][1]));
	//ei := Matrix(n,1,basis[i]);
        for m in [1..n] do
            for r in [1..n] do
                sum:=0;
                for i in [1..n] do
                    el:=X[i];
                    for j in [1..n] do
                        for k in [1..n] do
                            coeff:=el[j][k]*A[l][i]*B[m][j]*C[r][k];
                            sum:=sum+coeff;
                        end for;
                    end for;
                end for;
            mat[m][r]:=sum;
            end for;
        end for;
    el:=[*mat*];
    lst:=lst cat el; 
end for;
return lst;      
end function;

InvMatrix := function(n) // computes a random invertible matrix
	A := Matrix(n,n,[Random(F):i in [1..n^2]]);
	Z := Parent(M[1][1]);
	while Z!Determinant(M) eq 0 do 
		A := Matrix(n,n,[Random(F):i in [1..n^2]]);
	end while;
	return A;
end function;

// chooses random secret key values for secret key
keygen := function()
	b := Random([0,1]); 
	A := InvMatrix(n);
	B := InvMatrix(n);
	C := InvMatrix(n);
	return A,B,C,b;
end function;


// used to compute public key given a secret key
Commitment := function(A,B,C,b)
	sum:=0;
    lst:=[**]; // empty list 
	for i in [1..n] do
        mat:=identity(n,Parent(A[1][1]));
        for j in [1..n] do
            for k in [1..n] do
                sum:=0;
                for s in [1..(n-b)] do //changing order of the s sum doesn't change input 
                    coeff:=A[i][s]*B[j][s]*C[k][s];
                    sum:=sum+coeff;
                end for;
                mat[j][k]:=sum;
                //at the end of this loop sum is the coeff at the i,j,k spot of the nxnxn array
            end for;
        end for;
        el:=[*mat*];
        lst:=lst cat el;
	end for;
	return lst; // returns a n list of nxn matrices representing the output of the action 
end function;
