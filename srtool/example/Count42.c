// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"
int s;

int foo(int a, int b)
{
// 	int j;
	int i;
// 	i=501;
// 	assert(1==1);
// 	j=1;
// 	i=i/(j-j);
// // 	if (i == 0) {
// // 		j = 2;
// // 	}
// // 	else {
// // 		i = 1;
// // 	}
// 	i=-1*2;
// 	i=2*i;
// 	if (i != 0) {
// 		i=2;
// 		if(i !=0){
// 				i = 3;
// 			}else{
// 				i=4;
// 			}
// 		}
// 	else {
// 		i = 1;
// 	}
// 	return 0;
// 	i=-2;
	i=(1>2)?(2>1):0;
// 		i=1+1;
// 	i=(1>=1)+2+(1<2)+(3>2)+(4<=5);
// 	i=(1>(1>2))+1;
// 	i=2+1;
	return i+4;
}