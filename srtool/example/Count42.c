// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"
int s;

int foo(int a, int b)
{
	int i;
// 	i=2+2*3/5%4-5*3/2;
// 	i=(3+4)*(5+6);
// 有问题
// AssExpr:(+(-(*2 (+3 4)) 100) (%(-(+4 (~ (-1 2))) (/2 2)) 5))
	i=2*(3+4)-100+(4+2/2-~(1-2))%5;
//    (-(+4 (/2 2)) (-1 2))
// 	i=(1+2)-(4+2/2-(1-2));
// 	i=(1+1)+2;
// 	i=1*2/3;
// 	i=4+2/2-~(1-2);
// i=4+2/2-(1-2);
//		i=!~-+(1);
// 		i=!-~(1+2);
// 		i=1+2*3-4;
// 		i=3*4/5;
// 	i=2*(3+4)/3%(6-7);
// 	i=(2+(-1));
// 	i=4294967298;
// 	i=3;
// 	i=1+2*2%6/2*7;
// 	i=3;
// 	i=i+2+1+3;
// 	a=1;
// 	assert(42==42);

	return 0;
}