// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int blarp() {
    int a; int b; int c; int d; int e; int f;
    assume a == b;
    assume a == c;
    assume a != d;
    assume b != e;
    assume c != f;

    int temp;

    temp = a;
    a = b;
    b = c;
    c = temp;

    temp = d;
    d = e;
    e = f;
    f = temp;

    assert a == b;
    assert a == c;
    assert a != d;
    assert b != e;
    assert c != f;
    return 2;    
}
