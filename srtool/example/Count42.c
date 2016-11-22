// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"
int main(){
	int i;
	i=0;
	while(i<5){
		i=i+1;
		assert(1>2);
	}
	return 0;
}
