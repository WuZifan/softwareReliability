// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"
// int s;
int s;
int foo(int a, int b)
 requires a!=0,
 ensures \result == 4,
 ensures \result == 2
// requires a!=0
{
 	int i;
 	i = 1;
	assert(3<4);
	assert(2<3);
	assert(4<5);
	return 2;
}