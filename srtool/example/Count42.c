// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"
int s;

int foo(int a, int b)

{
	int j;
	int i;

	i = 1 << 5;
	return i;
}