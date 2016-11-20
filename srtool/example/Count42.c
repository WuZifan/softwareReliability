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



// RUN: %tool "%s" > "%t"

// RUN: %diff %CORRECT "%t"

int main(int i,int j,int z) {

	int a;

	int b;

	int c;

	int d;

	a=0; 

	b=0;

	c=0;

	d=0;

	if(i) {

	if(j) {

	a=1;

	} else {

	b=1;

	}

	} else {

	if(z) {

	c=1;

	} else {

	d=1;

	}

	}

	assert(!(i&&j)||(a&&!b&&!c&&!d));

	assert(!(i&&!j)||(!a&&b&&!c&&!d));

	assert(!(!i&&z)||(!a&&!b&&c&&!d));

	assert(!(!i&&!z)||(!a&&!b&&!c&&d));

	return 0;

}