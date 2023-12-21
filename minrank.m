clear;

// magma code for the minrank computation from https://arxiv.org/pdf/2002.08322

// Utility functions ----------------


Decompose:=function(M,r) //TODO--------------------------------
//decompose M as M=SC, S is nxr and C is rxm
//S is a basis for the column space 
//C has full rank r
end function;

MakeCdash := function(M,C,j) // build C_j' by adding the jth row of M as1st row and then C below
    rj:=M[j]; //select jth row of M
    Cdash:=VerticalJoin(rj,C);// rj is placed on top of C
    return Cdash;
end function; //checked 

MakeSubsets := function(n,r) // creates all possible subsets of size n-r of n 
    T := Subsets( {1 .. n}, n-r);
    return SetToSequence(T); // !!! returns a seq that contains sets 
end function; 

MakeSubmatrix:=function(M,T,r) // given a matrix M and a subset of indices T, remove all the columns for indices contained in T
    //seq_col:=SetToSequence(T);
    seq_col:=T;
    seq_row:=[i : i in [1..r]];
    A:=Submatrix(M,seq_row,seq_col);
return A;
end function;

//functions below need to be checked--------------------------------------------------
CofactorExp:=function(Cdash,C,T)//computes cofactor expansion with respect to 1st row 
    seq:=SetToSequence(T);
    temp:=0;
    for m in seq do 
        A:=MakeSubmatrix(C,T,3);
        temp:=temp+(-1)^(1+m)*C[1,m]*Determinant(RemoveColumn(A,m)); 
    end for;
end function;

BuildSupportMinors := function(M,r) // given a matrix,M, and a target rank, r, create the alg equations from support minors
    //construct S,C 
    S,C:=Decompose(M)
    //create empty seq for equations 
    eqns:=[]
    //build C_j and express each max minor
    T=MakeSubsets(n,r)
    for j in [1..n] do
        Cdash:=MakeCdash(M,C,j); //for each j buil C_j
        for el in T do //for each possible maximal minor of C_j compute Cofactor expansion
            eqns cat:=[CofactorExp(Cdash,C,el)]    
        end for;
    end for;
    return eqns
end function;

//-------------------------------------------------



// given a matrix,M, and a target rank, r, create the alg equations from support minors
BuildSupportMinors := function(M,r)

end function;

// given a list L of n square t x t matrices, compute the lin. comb. of matrices whose rank is leq r
ComputeMinRank := function(L)
	r := 1; // we only care about having target rank 1

	// set up the instance of minrank -------------
	n := #L; // number of matrices
	t := #Rows(L[1]); // dim of matrices in L
	F := Parent(L[1][1][1]); // determine base field
	P<[X]> := PolynomialRing(F,n+t); // create polynomial ring with variables x_i (=X[1..n]), but also the c_T (=X[n+1..n+t])

	M := ZeroMatrix(F,t); // create a matrix storing the desired lin. comb. in terms of the new variables, i.e. x1 M1 + ...xn Mn
	for i in [1..n] do 
		M := M + X[i]*L[i];
	end for;

	// compute equations to be solved using support minors --------
	eqns := []; // store here the equations we build
	for i in [1..t] do // for each row in M
		for j in [1..t] do 
			for k in [1..t] do
				if j lt k then // get all n choose 2 combinations of rows
					temp := M[i][j]*X[k+n] - M[i][k]*X[j+n]; // determinant should be zero
					eqns := eqns cat [temp];
				end if;
			end for;
		end for;
	end for;
	eqns := eqns cat [X[n]-1]; // force last coordinate to be 1
	// solve the equations we've gathered
	I := Ideal(eqns);
	sol := Variety(I);
	return sol;
end function;

// t is dim of square matrices, r is target minrank, F is base field
MakeList := function(t,F) 
	// generate list of t x t matrices
	L := [];
	for i in [1..t] do 
		M := RandomMatrix(F,t,t);
		L := L cat [M];
	end for;
	return L;
end function;


CheckSol:= function(sol, L)
//given a list of L matrixes and coeffs in sol check whether rank of sum(x_i)L_i is <=1 
	n := #L; // number of matrices
	t := #Rows(L[1]); // dim of matrices in L
	sum:=ZeroMatrix(F,t,t);
		for i in [1..n] do
			sum:=sum+sol[i]*L[i];
			sum;
		end for;
	return Rank(sum);
end function;

L := MakeList(2,GF(5));
L;
sols:=ComputeMinRank(L);

m:=#sols;
for i in [1..m] do 
    CheckSol(sols[m],pk);
end for;

//using CheckSol we observe that we sometimes get rank 2 stuff :( )
// for n=2, q=7 always get 13,19,49 or 91 sols

