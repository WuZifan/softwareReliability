// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"
int s;
int foo(int a)
{
	int i;

	int j;
	
	j=1;
	
	if (1 == 0) {
		j = 2;
	}
	else {
		i = 1;
		
	}
// 	i=4294967298;
// 	i=3;
// 	i=1+2*2%6/2*7;
// 	i=3;
// 	i=i+2+1+3;
// 	a=1;
// 	assert(42==42);
	return 0*1;
}