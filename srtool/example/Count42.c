// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"
int s;

int foo(int a)
{
	int i;
	i=4294967294;
	i=3;
	
	assert(42==42);
	return a;
}