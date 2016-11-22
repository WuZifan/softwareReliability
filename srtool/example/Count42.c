// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

// int s;
int y;
int x;
int s;

int bar(int h)
ensures \result <= \old(x){
	return h;
}

int foo(int a, int b)
 requires a!=0,
 requires b!=0,
//  ensures 4 == 4,
 ensures \result <= \old(x)
// requires a!=0
{
 	int i;
 	x=1;
 	i = 2;
//  	if(1==1){
// 		assert(3<4);
// 		i=2;
// 	}else{
// 		i=3;
// 	}
	s=1;
	i = bar(x);
	i = s;
	return x;
}


