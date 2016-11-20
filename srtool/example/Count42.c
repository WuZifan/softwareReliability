// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"
// int s;
int s;
int foo(int a, int b)
 requires a!=0,
 requires b!=0,
//  ensures 4 == 4,
 ensures \result > 3
// requires a!=0
{
 	int i;
 	i = 1;
//  	if(1==1){
// 		assert(3<4);
// 		i=2;
// 	}else{
// 		i=3;
// 	}
// 	assert(2<3);
	assume( 1 == 1);
	i = bar(i,9);
	assert(4<5);
	return i;
}

int bar(int a, int b)
 requires a!=0,
 ensures \result == 3
// requires a!=0
{
 	int i;
 	int j;
 	i = 1;
//  	if(1==1){
// 		assert(3<4);
// 		i=2;
// 	}else{
// 		i=3;
// 	}
	assert(4<5);
	return 32;
}