// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int y;

int foo() {
    int i;
    y = i;
    i = i - 2;
    assert(i == y - 2);
    return y - y;
}
