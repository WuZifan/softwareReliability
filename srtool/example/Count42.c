// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"
// int s;
int y;
int x;
int s;


int c;
int  foo(int a) {
// c = bar();
// assert(1>2);
	int i;
	i=0;
while(i<5){
	i=i+1;
}
return 2;
}

// int bar() 
// ensures \result != c{
// return c + 1;
// }
