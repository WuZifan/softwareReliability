// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int y;

int foo() {
    int i; int j;
    int k;
    int l;

    l = k ? 1 : 1;
    
    k = l || i;

    i = k || y || (i || j);

    j = i || i;

    assert(l);
    assert(k);
    assert(i);
    assert(j);
    assert y || k;
    return 0;
}
