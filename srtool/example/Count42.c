// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"
int main(){
	
	int m;
	int n;
	int a;
	int i;
	assume(m>=6);
	assume(m<=8);
	assume(n>=4);
	assume(n<=6);
	a=0;
	i=m;
	while(i>0){
		i=i-1;
		a=a+n;
	}
	assert(a==m*n);
	return 3;
}



