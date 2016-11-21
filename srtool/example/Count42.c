// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int foo() {
	int i;
	int j;
	i=42;
	j=~i;
	assert(j<0);
	return 3;
}
