
clear; 

load "group-action.m";

// attacking DTI variant using rank 0 points

// given a public key generated from keygen(), recovers the secret bit b
RankAttack := function(pk)
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


//A,B,C,b := keygen();
//pk := Commitment(A,B,C,b);
//time b1 := RankAttack(pk);
//b1 eq b;
