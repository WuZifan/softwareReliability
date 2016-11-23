// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int main(){
	int i;
	i=0;
	int j;

	if(i == 1) {
		i = 1;
	}
	i=42;
	j=~i;
	assert(j<0);
	return 3;
}

int bar(){
	
	return 0;
}

int foo(){
	assert(2<1);
	return 1;
}
