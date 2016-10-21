// RUN: %tool "%s" > "%t"
// RUN: %diff %INCORRECT "%t"

int foo(int i, int j)
    requires j >= 31,
    ensures \result == 0
{
    return i << j;
}
