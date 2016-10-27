// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"
int s;

int foo(int a, int b)
{
	int j;
	int i;
	assert(1==1);
	j=1;
	if (i == 0) {
		j = 2;
	}
	else {
		i = 1;
	}
	return 0;
}