// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"
int s;

int foo(int a, int b)
 requires a!=0,
 requires b > 0,
 ensures \result == 1
// requires a!=0,
// requires b > 0,
// ensures \result == 0
{
 	int i;
// 	i=(1>2)?(2>1):0;
//  	assume(1==1);
 	i = 1;
	assert(3<4);
// 	if(1==1){
// 			//if(2==2){
// 				assert(2>1);
// // 			}else{
// // 				assert(5>4);
// // 			}
// 	}
// 	else{
// 		if(3==3){
// 			assert(4>3);
// 		}else{
// 			assert(3>2);
// 		}
// 	}
	return i;
}