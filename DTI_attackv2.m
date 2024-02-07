clear; 

load "group-action.m";

// attacking DTI variant using rank 0 points version 2 : sampling a random pointand checking whether it has full rank (b=0 case) or not (b=1 case)


RankAttack:=function(pk);
u:= RandomMatrix(F,1,n); // sample a random point 
M:=ZeroMatrix(F,n);
for i in [1..n] do 
    M1:=u[1][i]*pk[i];
    M+:=M1;
end for;
r:=Rank(M); // check the resulting rank 
if r eq n then 
    return 0;
end if;
return 1;
end function;

ctr:=0;
for i in [1..50] do
    A,B,C,b:=keygen();
    pk:=Commitment(A,B,C,b);
    b1:=RankAttack(pk);
    if b eq b1 then 
        ctr+:=1;
    end if;
end for;
ctr;
