// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int iffy(int i)
  ensures \result >= i
{
    int t;
    t = i;
    if(i < (1 << 24)) {
        t = i + 1;
    }
    return t;
}
