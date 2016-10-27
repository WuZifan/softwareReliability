// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"
int s;

int foo(int a, int b)
requires a>0,
requires b<0,
ensures \result==0,
ensures \result==2
{
	int j;
	int i;
	i=501;
	j=1;
	i=i/(j-j);

	if (j != 0) {
		j = 2;
	}
	else {
		i = 1;
	}
	
	return i;
}