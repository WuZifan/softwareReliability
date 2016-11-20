// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"
// int s;
// int s;
// int foo(int a, int b)
//  requires a!=0,
//  requires b!=0,
// //  ensures 4 == 4,
//  ensures \result == 32
// // requires a!=0
// {
//  	int i;
//  	int j;
//  	i = 1;
//  	j=2;
//  	assert(4<5);
//  	if(1==1){
// 		i=2;
// 	}else{
// 		i=3;
// 	}
// 	i=(i)&&(j);
// 	assert(2<3);
// 	
// 	assert(4>6);
// 	return 32;
// }



int flump;
int __cl3nk()
ensures \result==flump+(16<<1)
{
	int x;
	x=1;
	int i;
	i=0;
	
	i=4;
	x=32;
	  if(i<5)
	  { x=x+1; //x=33
	  i=i+1; //i=5
	  }
	  if(i<5)
	  {
	  assume 4==5;
	  x=x+1;
	  i=i+1;}
	  if(i<5)
	  {
	  assert 0;
	  x=x+1;
	  i=i+1;
	  }
	  assert x==32;
	  return x+flump;
	  }

