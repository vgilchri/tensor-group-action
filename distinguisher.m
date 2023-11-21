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

GACE := function(A,B,C,b)
// input: n x n matrices A,B,C and a bit b
// output: a sum of tensors relying on the input
	basis := identity(n,P);
	max := n-b; // the bit determines whether to include the last tensor or not
	sum := 0; // compute actual group action: a sum of tensors
	for k in [1..max] do 
		ei := Matrix(n,1,basis[k]); // make the basis vectors matrix type
		termA := A*ei;
		termB := B*ei;
		termC := C*ei;
		tensor1 := TensorProduct(termA,termB);
		tensor2 := TensorProduct(tensor1,termC);
		if sum eq 0 then
			sum := tensor2;
		else 
			sum := sum + tensor2;
		end if;
	end for;
	return sum;
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

//tensor_prod(u,v,w);
//tsr1:=TensorProduct(Matrix(F,n,1,v),Matrix(F,n,1,w));
//TensorProduct(tsr1,Matrix(F,n,1,u))

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


//Testing 
"key";
A,B,C,b := keygen(); // for now b is always 0
A;
B;
C;

JouxAction(A,B,C);
JouxAction_NEW(A,B,C);



//----------------------------------------------------------------------------
//TODO: Implement Star

star := function(A,B,C,X)
// performs the general group action (A,B,C)*X
//Assume X is represented using our tensor product representation as above. 
sum:=0;
lst:=[**];
for l in [1..n] do
    mat:=identity(n,F);
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

//sanity check on def of t_b
basis := identity(n,P);
t_b:=0;
for i in [1..n] do
    ei := Matrix(n,1,basis[i]);
    tsr1:=TensorProduct(ei,ei);
    tsr2:=TensorProduct(tsr1,ei);
    if t_b eq 0 then 
		t_b:= tsr2; 
	else 
		t_b:= t_b + tsr2;
	end if;
end for; 


//testing 
I:=identity(n,P);
t_b:=JouxAction_NEW(I,I,I); //check if def of tb is right ? 
"t_b";
t_b;
"result of star";
pk:=star(A,B,C,t_b); // it works!!!!
pk;
"result of GACE";
GACE(A,B,C,0);
"result of Joux Action on tb";
JouxAction(A,B,C); 


distinguisher := function(pk,M)
//assume we are given an invariant matrix M for b=0
//given a public key pk check whether (M,M,M)*pk=pk to decide on the bit 
"pk";
pk;
out:=star(M,M,M,pk);
"out";
out;
//return out eq pk; //not quite the same but some interesting symmetries... 
end function; 

M:=Matrix(2,2,[P!0,P!1,P!1,P!0]);
distinguisher(pk,M)