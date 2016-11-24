// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"
// int s;
// int y;
// int x;
// int s;
// 
// 
 int c;
int foo(int a) {
	
	int i ;
 	c = bar(c);
 	assert(1>2);
	return 1;
}

int bar(int a) 
ensures \result != c{
	return c + 1;
}
