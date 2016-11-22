// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"
int main(){
	
	int i;
	i=0;
	while(i<2){
		i=i+1;
	}
	return 3;
}

int bar(){
	
	return 0;
}

int foo(){
assert(2<1);	
	return 1;
}
