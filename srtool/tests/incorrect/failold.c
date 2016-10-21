// RUN: %tool "%s" > "%t"
// RUN: %diff %INCORRECT "%t"

int x;
int y;

int foo(int i)
    requires x == y + 1,
    ensures y == \old(x),
    ensures \result == \old(x)
{
    if(x == y + 1) {
        y = y - 1;
    }
    return x;
}
