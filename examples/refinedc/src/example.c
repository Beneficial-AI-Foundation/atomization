unsigned int add3(unsigned int x, unsigned int y, unsigned int z) {
  unsigned int r = x + y;
  return r + z;
}

unsigned int add4(unsigned int x, unsigned int y, unsigned int z,
                  unsigned int w) {
  unsigned int r = x + y;
  unsigned int s = z + w;
  return r + s;
}

unsigned int add5(unsigned int x, unsigned int y, unsigned int z,
                  unsigned int w, unsigned int v) {
  unsigned int r = x + y;
  unsigned int s = z + w;
  return r + s + v;
}
