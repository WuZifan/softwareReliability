// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"
<<<<<<< HEAD

int foo() {
=======
int main(){
>>>>>>> branch 'master' of https://github.com/w460461339/softwareReliability.git
	int i;
	int j;
	i=42;
	j=~i;
	assert(j<0);
	return 3;
<<<<<<< HEAD
}
=======
}
>>>>>>> branch 'master' of https://github.com/w460461339/softwareReliability.git
