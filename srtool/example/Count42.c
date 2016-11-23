// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"
// int s;
int y;
int x;
int s;



int bar(int h)
ensures \result != x{
	int i;
	i=c(9);
	return x+1;
}

int foo(int a, int b)
 requires a!=0,
 requires b!=0,
//  ensures 4 == 4,
 ensures \result <= \old(x)
// requires a!=0
{
 	int i1;
 	i1 = 2;
//  	if(1==1){
// 		assert(3<4);
// 		i=2;
// 	}else{
// 		i=3;
// 	}
	s=1;
	s = bar(x);
	i1 = s;
	return x;

}

int c(int h)
requires h<10
{
	int i;
	return h+1;
}
