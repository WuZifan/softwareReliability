// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"
int main(){
	int i;
	int j;
	j=0;
	i=0;
	while(i<3){
		i=i+1;
	}
	return 0;
}
