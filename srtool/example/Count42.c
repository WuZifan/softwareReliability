// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"
int main(){
	int i;
	i=0;
	int j;
	j=0;
	if(2<3){
		while(i<5){
			i=i+1;
			while(j<2){
				j=1+j;
			}
		}
	}
	return 0;
}
