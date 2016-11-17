// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"
int s;

int foo(int a, int b)
 requires a!=0,
 requires b > 0,
 ensures \result == 1
// requires a!=0,
// requires b > 0,
// ensures \result == 0
{
 	int i;
// 	i=(1>2)?(2>1):0;
//  	assume(1==1);
	i=bar( (2+1)/3 );	
	return 2;
}

int bar(int a){
	return 0;
}