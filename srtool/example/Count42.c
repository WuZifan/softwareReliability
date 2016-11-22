// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int main(){

	int a;
	a=0;
	while(a<2)
	{
		a=a+1;		
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
