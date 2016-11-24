// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int foo(int x, int y) 
  requires y > 32
{
  int s;
  int t;
  s = x;
  t = y;
  while(t > -42)
      invariant t >= -42,
      invariant (t == y || s == 0) {
    s = s << t;
    assert s == 0;
    t = t - 1;
  }
  assert s == 0;
  assert t == -42;
  return 0;
}