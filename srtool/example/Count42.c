// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"
int s;

int foo(int a, int b)
requires a!=0,
requires b<0,
ensures \result > 0,
ensures \result ==2
{
	int j;
	int i;
	i=-2;
	i=-1*2;

	
	return i+4;
}