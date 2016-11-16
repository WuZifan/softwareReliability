// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"
int s;

int foo(int a, int b)
 requires a!=0,
 requires b > 0,
 ensures 0 == 0
{
	s=s+1;
	assert(3>4);
	assert(\old(s)>1);
	return 1;
}