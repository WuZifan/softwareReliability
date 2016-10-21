// RUN: %tool "%s" > "%t"
// RUN: %diff %INCORRECT "%t"

int foo() {

    int x;
    int y;
    x = 501;
    y = x - x;
    int z;
    z = x / y;
    assert z == 0;
    return 0;

}
