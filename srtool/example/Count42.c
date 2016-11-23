// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"
int main(){
	
	int i;
	i=0;

	while(i<1000){
		i=i+1;
	}
	int j;
	j=bar();
	return 3;
}

int foo(){
	assert(2>1);	
	return 1;
}

int bar()
//  ensures \result!=0
{
	
	return 0;
}


