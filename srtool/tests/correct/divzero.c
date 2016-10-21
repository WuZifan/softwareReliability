// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int foo() {

    int x;
    int y;
    x = 501;
    y = x - x;
    int z;
    z = x / y;
    assert z == 501;
    return 0;

}
