clear;

load "rank0attack.m";

// magma code for the minrank computation from https://arxiv.org/pdf/2002.08322


//-------------------------------------------------


// given a list L of n square t x t matrices, compute the lin. comb. of matrices whose rank is leq r
ComputeMinRank := function(L)
	r := 1; // we only care about having target rank 1

	// set up the instance of minrank -------------
	n := #L; // number of matrices
	t := #Rows(L[1]); // dim of matrices in L
	F := Parent(L[1][1][1]); // determine base field
	P<[X]> := PolynomialRing(F,n+t); // create polynomial ring with variables x_i (=X[1..n]), but also the c_T (=X[n+1..n+t])

	M := ZeroMatrix(F,t); // create a matrix storing the desired lin. comb. in terms of the new variables, i.e. M = x1 M1 + ...xn Mn
	for i in [1..n] do 
		M := M + X[i]*L[i];
	end for;

	// compute equations to be solved using support minors --------
	eqns := []; // store here the equations we build
	for i in [1..t] do // for each row in M
		for j in [1..t-1] do // choose the first column
			for k in [j+1..t] do // choose the second column
				temp := M[i][j]*X[k+n] - M[i][k]*X[j+n]; // determinant should be zero
				eqns := eqns cat [temp];
			end for;
		end for;
	end for;
	eqns := eqns cat [X[n]-1,X[n+1]-1]; // force last coordinate to be 1
	// solve the equations we've gathered
	I := Ideal(eqns);
	sol := Variety(I);
	return sol;
end function;

// t is dim of square matrices, r is target minrank, F is base field
// generate random instance to input into minrank
MakeList := function(t,F) 
	// generate list of t x t matrices
	L := [];
	for i in [1..t] do 
		M := RandomMatrix(F,t,t);
		L := L cat [M];
	end for;
	return L;
end function;

// determine whether result from minrank gives a matrix of appropriate rank
CheckSol := function(sol, L)
//given a list of L matrixes and coeffs in sol check whether rank of sum(x_i)L_i is <=1 
	n := #L; // number of matrices
	t := #Rows(L[1]); // dim of matrices in L
	F := Parent(L[1][1][1]);
	sum:=ZeroMatrix(F,t,t);
		for i in [1..n] do
			sum:=sum+sol[i]*L[i];
		end for;
	return Rank(sum);
end function;

// generate random instance, and compute min rank
Example := function()
	
	A,B,C,b := keygen();
	L := Commitment(A,B,C,b);
	//L := MakeList(2,GF(5));
	sols:=ComputeMinRank(L);

	check := true;
	m:=#sols;
	for i in [1..m] do 
    	temp := CheckSol(sols[i],L) lt 2;
    	check := check and temp;
	end for;
	return check;
end function;

star := function(A,B,C,X)
// performs the general group action (A,B,C)*X
//Assume X is represented using our tensor product representation as above. 
sum:=0;
lst:=[**];
for l in [1..n] do
    mat:=identity(n,Parent(A[1][1]));
	//ei := Matrix(n,1,basis[i]);
        for m in [1..n] do
        //ej := Matrix(n,1,basis[j]);
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
        //"matrix in a list";
       // el;
    lst:=lst cat el; 
end for;
return lst;      
end function;

A,B,C,b := keygen();
L := Commitment(A,B,C,0);
//L := MakeList(2,GF(5));

// given a public key (tensor) L, find A,B,C such that (A,B,C) star t_0 = L
CompAttack  := function(L)
	pts:=ComputeMinRank(L);
	if #pts lt n then // check there are enough rank 1 points
		return "error: not enough rank 1 points. try again.";
	end if;
	lst := [];
	for i in [1..n] do // with rank 1 points, build a matrix
		lst := lst cat [pts[i][j]:j in [1..n]];
	end for;
	//A := Transpose(Matrix(n,n,lst)); // ? do we want the points as rows or columns ?
	A := Matrix(n,n,lst);
	// poly ring
	R<[X]> := PolynomialRing(F,2*n^2); // vars for B1 and C1-inv
	// (I,B1,I) star (A1,I,I) star t_0
	I1 := identity(n,R); // make id matrix
	f1 := Commitment(A,I1,I1,0);
	B1 := Matrix(n,n,[X[i]:i in [1..n^2]]);
	LHS := star(I1,B1,I1,f1);
	//LHS := Commitment(A1,B1,I1,0);
	// (I,I,C1^inv) star L
	D1 := Matrix(n,n,[X[i]:i in [n^2+1..2*n^2]]);
	RHS := star(I1,I1,D1,L);
	// solve vars
	eqns := [];
	for i in [1..n] do // make equations by subtracting tensors
		for j in [1..n] do 
			for k in [1..n] do 
				eqns := eqns cat [LHS[i][j][k] - RHS[i][j][k]];
			end for;
		end for;
	end for;
	I := Ideal(eqns); // solve equations (should be linear) with Groebner basis
	sols := Variety(I);
	B := Matrix(n,n,[sols[1][i]:i in [1..n^2]]);
	C := Matrix(n,n,[sols[1][i]:i in [n^2+1..2*n^2]]);
	return A,B,C;
end function;

CompAttack(L);

// problems: 
// -> MinRank works for small parameters, but times out for big ones
// -> the attack is not working, always gives 0 solutions for B, C -- LM : maybe we should enforce det\neq 0 again
// -> also the A it recovers using MinRank seems to not work...
//    I get that Commitment(A,I,I,0) != Commitment(A1,I,I,0)
