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

// run test 100 times, print what percent were correct
success := 0;
for i in [1..100] do 
	x := Example();
	if x eq true then 
		success := success + 1;
	end if;
end for;
success;
