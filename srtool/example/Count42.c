

// RUN: %tool "%s" > "%t"

// RUN: %diff %CORRECT "%t"

int main(int i,int j,int z) {
	
	int a;
	a=1;
	assert(1<2);
	assume(2>3);
	assert(1>2);
	return 0;
}