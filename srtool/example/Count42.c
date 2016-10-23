// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int foo(int a)
{
	int i;
	i=4294967298;
	i=3;
	a=1;
	assert(42==42);
	return a;
}