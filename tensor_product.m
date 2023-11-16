n := 2;
q := 11;
F := FiniteField(q);
vars_num := 3*n^2; // can put this later in attack function
P<[X]> := PolynomialRing(F,vars_num); // define a polynomial ring for unknown values
gens := <X[i] : i in [1..vars_num]>; // name all the variables we need to solve for


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

IsInvertible := function(M)
	Z := Parent(M[1][1]);
	det := Determinant(M);
	det := Z!det;
	if det eq 0 then 
		return false;
	end if;
	return true;
end function;

InvMatrix := function(n)
	A := Matrix(n,n,[P!Random(F):i in [1..n^2]]);
	while IsInvertible(A) eq false do 
		A := Matrix(n,n,[P!Random(F):i in [1..n^2]]);
	end while;
	return A;
end function;

keygen := function()
// chooses random secret key values, and computes the corresponding public key
	b := 0;
	A := InvMatrix(n);
	B := InvMatrix(n);
	C := InvMatrix(n);
	//pk := GACE(A,B,C,b);
	return A,B,C,b; //,pk;
end function;


//--------------------------------------------------------------------
// Implemented our own tensor product 


tensor_prod := function(u,v,w)
// return the tensor product of u,v,w of dim n as an n x n x n array 
//assume the input vectors are array of coefficients with respect to the canonical basis of F_q^n
	tsr := Matrix(F,n,1,v)*Transpose(Matrix(F,n,1,w)); //tested and works 
	tsr;
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

u:=[1,2,3];
v:=[4,5,6];
w:=[7,8,9];

tensor_prod(u,v,w);
tsr1:=TensorProduct(Matrix(F,n,1,v),Matrix(F,n,1,w));
TensorProduct(tsr1,Matrix(F,n,1,u))

//----------------------------------------------------------------------------
//TODO: Implement GACE using homemade tensorproduct -> need to do it using the coefficient formula i.e. our JouxACtion 
//DONE

JouxAction := function(A,B,C)
	basis:=identity(n,P);
	sum:=0;
	for s in [1..n] do
		for i in [1..n] do
		ei := Matrix(n,1,basis[i]);
			for j in [1..n] do
			ej := Matrix(n,1,basis[j]);
				for k in [1..n] do
				ek := Matrix(n,1,basis[k]);
				coeff:=A[i][s]*B[j][s]*C[k][s];
				tsr1 := TensorProduct(ei,ej);
				tsr2 := TensorProduct(tsr1,ek);
				term := coeff*tsr2;
				if sum eq 0 then 
					sum:= term; 
				else 
					sum:= sum + term;
				end if;
				end for;
			end for;
		end for;
	end for;
	return sum; 
end function;

JouxAction_NEW := function(A,B,C)
	basis:=identity(n,P);
	sum:=0;
    lst:=[**]; // empty list 
    //need to initialize an empty array to fill ?
	for i in [1..n] do
	//ei := Matrix(n,1,basis[i]);
        mat:=identity(n,F);
        for j in [1..n] do
        //ej := Matrix(n,1,basis[j]);
            for k in [1..n] do
                sum:=0;
                for s in [1..n] do //changing order of the s sum doesn't change input 
                    //ek := Matrix(n,1,basis[k]);
                    coeff:=A[i][s]*B[j][s]*C[k][s];
                    "Coeff";
                    coeff;
                    sum:=sum+coeff;
                end for;
                mat[j][k]:=sum;
                "Current matrix";
                mat;
                //at the end of this loop sum is the coeff at the i,j,k spot of the nxnxn array
            end for;
        end for;
        el:=[*mat*];
        "matrix in a list";
        el;
        lst:=lst cat el;
        "list";
        lst;
	end for;
	return lst; // returns a n list of nxn matrices representing the output of the action 
end function;


//Testing 
A,B,C,b := keygen(); // for now b is always 0

JouxAction(A,B,C)
JouxAction_NEW(A,B,C)



//----------------------------------------------------------------------------
//TODO: Implement Star

star := function(A,B,C,elt)
// performs the general group action on two inputs
// not sure how this is done in the real world
// but the paper assumes it can be done, so we will assume the same
// !!!!!!!!!!!!! for now we assume the structure of the GACE but this should be generalized later !!!!!!!!!!!!!!!!!!!!!!
	action := GACE(A,B,C,0); // compute \Sigma A*e_i \otimes B*e_i \otimes C_e_i
	for i in [1..n^3] do 
		action[i] := action[i]*elt[i]; // scalar multiply relevant coefficients from input class group
	end for;
	return action;
end function;
