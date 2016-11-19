// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"
// int s;
int s;
int foo(int a, int b)
 requires a!=0,
 requires b!=0,
//  ensures 4 == 4,
 ensures \result == 32
// requires a!=0
{
 	int i;
 	int j;
 	i = 1;
 	j=2;
 	if(1==1){
		i=2;
	}else{
		i=3;
	}
	i=(i)&&(j);
	assert(2<3);
	assert(4<5);
	return 32;
}