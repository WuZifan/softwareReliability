// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"
int s;

int foo(int a, int b)
{
	int j;
	int i;
	i=501;
// 	assert(1==1);
	j=1;
	i=i/(j-j);
// 	if (i == 0) {
// 		j = 2;
// 	}
// 	else {
// 		i = 1;
// 	}
	return 0;
}