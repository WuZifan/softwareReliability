// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int iffy(int i, int j)
  requires i == j
{
    int x;
    int y;
    x = i;
    y = j;
    if(x < (1 << 24)) {
        x = x + 1;
        y = y + 1;
    } else {
        if(x > 24) {
            x = x + y;
            y = y + y;
        }
    }
    assert x == y;
    return 0;
}
