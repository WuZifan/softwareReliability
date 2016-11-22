// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

// int s;
int s;
int foo(int a, int b)
 requires a!=0,
 requires b!=0,
//  ensures 4 == 4,
 ensures \result <= 5
// requires a!=0
{
 	int i;
 	i = 2;
//  	if(1==1){
// 		assert(3<4);
// 		i=2;
// 	}else{
// 		i=3;
// 	}
	assert(2<3);
	assume(1>2);
	assert(2>5);
	
	while(i<=1)
	invariant i <= 2 {
		
		i=i-1;
		
	}
	return i;
}

int bar() {
	int i;
	int j;
	i=42;
	j=~i;
	assert(j<0);
	return 3;

}

