// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int main(){

	int i;
	int j;
	i=42;
	j=~i;
	assert(j<0);
	return 3;
}
