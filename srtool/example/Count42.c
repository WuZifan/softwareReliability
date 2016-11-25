// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int x;
int y;

int bar()
  ensures x == \old(x) + 1
{
  x = x + 1;
  return 0;
}

int main()
{
  x = 0;
  while(x < 10) {
    int t;
    t = bar();
  }
  assert x == 10;
  return 0;
}