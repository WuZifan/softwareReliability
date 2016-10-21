// RUN: %tool "%s" > "%t"
// RUN: %diff %INCORRECT "%t"

int y;

int foo() {
    int i;
    y = i;
    i = i - -2;
    assert(i == y - 2);
    return y - y;
}
