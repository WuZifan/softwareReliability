// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"
int main(){
	int i;
	i=0;
	while(i<1){
		i=i+1;
	}
	return 3;
}
