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
<<<<<<< HEAD
	i=501;
	assert(1==1);
	j=1;
	i=i/(j-j);
// 	if (i == 0) {
// 		j = 2;
// 	}
// 	else {
// 		i = 1;
// 	}
	if (j != 0) {
		j = 2;
	}
	else {
		i = 1;
	}
	return 0;
=======
	i=-2;
	i=-1*2;

	
	return i+4;
>>>>>>> branch 'master' of https://github.com/w460461339/softwareReliability.git
}