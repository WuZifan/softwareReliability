// RUN: %tool "%s" > "%t"
// RUN: %diff %INCORRECT "%t"

int foo() {
    assert 0;
    return 1;
}
