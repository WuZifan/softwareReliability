// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"
// int s;
int s;
int foo(int a, int b)
 requires a!=0,
//  ensures \result == 4,
 ensures \result == 3
// requires a!=0
{
 	int i;
 	int j;
 	i = 1;
 	if(1==1){
		assert(3<4);
		i=2;
	}else{
		i=3;
	}
	assert(2<3);
	assert(4<5);
	return 2;
}