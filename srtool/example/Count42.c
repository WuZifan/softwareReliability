// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int foo(int a)
{
	int i;
	i=2+2*3/5%4-5*3/2;
	int j;
	
	j=1;
// 	i=4294967298;
// 	i=3;
// 	i=1+2*2%6/2*7;
// 	i=3;
// 	i=i+2+1+3;
// 	a=1;
// 	assert(42==42);
	return 0*1;
}