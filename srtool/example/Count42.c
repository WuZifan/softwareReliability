// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int foo(int a)
{
	int i;
	i=-2;
	return a;
}