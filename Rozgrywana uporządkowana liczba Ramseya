#include <algorithm>
#include <array>
#include <bitset>
#include <cstdio>
#include <map>
#include <set>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>
using namespace std;
constexpr int
    V_MAX = 24,
    V_MAX_SQ =
        V_MAX * V_MAX; /// V_MAX=2n, bo jeĹ›li mamy n ruchĂłw, to zajmuje max 2
                       /// wierzchoĹ‚ki; V_MAX_SQ=V_MAX*V_MAX - wielkoĹ›Ä‡ macierzy.
typedef bitset<V_MAX_SQ> matrix;
int K, N;
struct interval {
  short l, r;
  interval() {
    l = -10; ///-10 oznacza, ĹĽe nie wiemy przy ilu ruchach jeszcze wygrywa
             ///malarz.
    r = 10000;
  }
};
unordered_map<matrix, interval>
    ANAL_POS; /// nieuporzÄ…dkowany sĹ‚ownik, ktĂłry przechowuje wszystkie moĹĽliwe
              /// pozycje w grze.

#define ST first
#define ND second
#define MP make_pair

matrix strictlyLowerTriangularMask() {
  matrix low;
  for (int i = 1; i < V_MAX; ++i)
    for (int j = 0; j < i; ++j)
      low[i * V_MAX + j] = 1;
  return low;
}
const matrix LOWER_MASK = strictlyLowerTriangularMask();
matrix strictlyUpperTriangularMask() {
  matrix upp;
  for (int i = 0; i < V_MAX; ++i)
    for (int j = i + 1; j < V_MAX; ++j)
      upp[i * V_MAX + j] = 1;
  return upp;
}
const matrix UPPER_MASK = strictlyUpperTriangularMask();
const array<matrix, V_MAX> rowMasks() {
  /// masks for each row of a matrix
  array<matrix, V_MAX> ver;
  int i = 0;
  for (i = 0; i < V_MAX; ++i)
    ver[0][i] = 1;
  for (i = 1; i < V_MAX; ++i)
    ver[i] = ver[i - 1] << V_MAX;
  return ver;
}
const array<matrix, V_MAX> ROW_MASKS = rowMasks();

const array<matrix, V_MAX> columnMasks() {
  /// masks for each column of a matrix
  array<matrix, V_MAX> ver;
  int i = 0;
  for (i = 0; i < V_MAX; ++i)
    ver[0][i * V_MAX] = 1;
  for (i = 1; i < V_MAX; ++i)
    ver[i] = ver[i - 1] << 1;
  return ver;
}
const array<matrix, V_MAX> COLUMN_MASKS = columnMasks();

const array<matrix, V_MAX + 1> sumMasks(array<matrix, V_MAX> masks) {
  /// masks for first k rows of a matrix
  array<matrix, V_MAX + 1> ver;
  int i = 0;
  for (i = 0; i < V_MAX; ++i)
    ver[i + 1] = ver[i] | masks[i];
  return ver;
}
const array<matrix, V_MAX + 1> S_ROW_MASKS = sumMasks(ROW_MASKS),
                               S_COLUMN_MASKS = sumMasks(COLUMN_MASKS);

struct Graph {
  matrix m;  /// adjacency matrix
  int e = 0; /// number of edges
  int v = 0; /// number of vertices
  void addEdge(int v1, int v2) {
    /// if v1<v2, edge is blue, otherwise red
    m[v1 * V_MAX + v2] = 1;
    ++e;
  }
  void removeEdge(int v1, int v2) {
    /// if v1<v2, edge is blue, otherwise red
    m[v1 * V_MAX + v2] = 0;
    --e;
  }
  void addVertex(int w) {
    m = (m & S_COLUMN_MASKS[w]) |
        ((m << 1) & (~S_COLUMN_MASKS[w + 1])); /// add a column
    m = (m & S_ROW_MASKS[w]) |
        ((m << V_MAX) & (~S_ROW_MASKS[w + 1])); /// add a row
    ++v;
  }
  void removeVertex(int w) {
    m = (m & S_COLUMN_MASKS[w]) |
        ((m >> 1) & (~S_COLUMN_MASKS[w])); /// delete a column
    m = (m & S_ROW_MASKS[w]) |
        ((m >> V_MAX) & (~S_ROW_MASKS[w])); /// delete a row
    --v;
  }
  void clear() {
    m.reset();
    v = 0;
    e = 0;
  }
  int matching() { /// finds the size of the biggest red matching
    auto g = m & LOWER_MASK;
    int i = 0, n = 0;
    while (1) {
      i = g._Find_next(i * V_MAX - 1) / V_MAX;
      if (i >= v)
        return n;
      ++n;
      g &= ~S_COLUMN_MASKS[i + 1];
    }
  }
  int path() { /// finds the number of vertices in the longest blue monotonic
               /// path
    auto g = m & UPPER_MASK;
    array<int, V_MAX> l{};
    int x, y, mx = 0;
#define FOR_BS(i, bset, beg, end)                                              \
  for (int i = (bset)._Find_next((beg)-1); i < end; i = (bset)._Find_next(i))
    FOR_BS(i, g, 0, V_MAX_SQ) {
      x = i / V_MAX;
      y = i % V_MAX;
      if (l[x] + 1 > l[y]) {
        l[y] = l[x] + 1;
        mx = max(mx, l[x] + 1);
      }
    }
    return mx + 1;
  }
  int paths() {
    auto g = m & UPPER_MASK;
    array<int, V_MAX> l{};
    int x, y, j = 1, mx = 0;
#define FOR_BS(i, bset, beg, end)                                              \
  for (int i = (bset)._Find_next((beg)-1); i < end; i = (bset)._Find_next(i))
    FOR_BS(i, g, 0, V_MAX_SQ) {
      x = i / V_MAX;
      y = i % V_MAX;
      for (; x >= j; ++j)
        l[j] = max(l[j], l[j - 1]);
      if (l[x] + 1 > l[y]) {
        l[y] = l[x] + 1;
        mx = max(mx, l[x] + 1);
      }
    }
    return mx + 1;
  }
  bool redInside(int i,
                 int j) { /// checks if there is a red edge in [i,j] interval
    return (m & LOWER_MASK & S_ROW_MASKS[j + 1] & ~S_ROW_MASKS[i] &
            S_COLUMN_MASKS[j + 1] & ~S_COLUMN_MASKS[i])
        .any();
  }
  int redDegree(int i) {
    return (m & LOWER_MASK & (ROW_MASKS[i] | COLUMN_MASKS[i])).count();
  }
};

void print(Graph G) {
#define FOR_BS(i, bset, beg, end)                                              \
  for (int i = (bset)._Find_next((beg)-1); i < end; i = (bset)._Find_next(i))
  FOR_BS(i, G.m, 0, V_MAX_SQ)
  printf("%d %d\n", i / V_MAX, i % V_MAX);
  printf(">>%d %d\n", G.matching(), G.path());
}
void print(matrix m) {
  for (int i = 0; i < V_MAX_SQ; ++i)
    printf(i % V_MAX == V_MAX - 1 ? "%d\n" : "%d", (int)m[i]);
  printf("\n");
}

bool colour(Graph G, int m, int i, int j, bool x, bool y);
bool construct(Graph G, int m) {
  /// returns 1 iff builder has a winning move
  // print(G);
  auto &x = ANAL_POS[G.m];
  if (x.l >= m)
    return 0;
  if (x.r <= m)
    return 1;
  int i, j, matching = G.matching(), paths = G.paths();
  if (matching >= K || G.path() >= N) {
    x.r = 0;
    return 1;
  }
  if (K - matching + max(N - paths - 1, 0) > m) {
    x.l = K - matching + max(N - paths - 1, 0) - 1;
    return 0;
  }
  if (m == 0) {
    x.l = m;
    return 0;
  }
  for (i = 0; i <= G.v; ++i)
    for (j = i; j <= G.v; ++j) {
      if (i != j && j < G.v) {
        if (colour(G, m, i, j, 0, 0)) {
          x.r = m;
          return 1;
        }
      }
      if (j < G.v) {
        if (colour(G, m, i, j, 1, 0)) {
          x.r = m;
          return 1;
        }
      }
      if (i < G.v) {
        if (colour(G, m, i, j, 0, 1)) {
          x.r = m;
          return 1;
        }
      }
      if (colour(G, m, i, j, 1, 1)) {
        x.r = m;
        return 1;
      }
    }
  x.l = m;
  return 0;
}
bool colour(Graph G, int m, int i, int j, bool x, bool y) {
  /// returns 0 iff painter has a winning move
  if (G.v + x + y > V_MAX)
    return 0;
  if (x) {
    G.addVertex(i);
    ++j;
  }
  if (y)
    G.addVertex(j);
  if (G.redInside(i, j))
  /// if Builder played a stupid move, call it a win for Painter
    return 0;
  if (G.redDegree(i) == 0 || G.redDegree(j) == 0) {
    G.addEdge(i, j);
    if (!construct(G, m - 1))
      return 0;
    G.removeEdge(i, j);
    G.addEdge(j, i);
    if (!construct(G, m - 1))
      return 0;
  } else {
    G.addEdge(j, i);
    if (!construct(G, m - 1))
      return 0;
    G.removeEdge(j, i);
    G.addEdge(i, j);
    if (!construct(G, m - 1))
      return 0;
  }
  return 1;
}

int main() {
  Graph G;
  K = 6;
  N = 5;

  for (int i = 0; i < 13; ++i){
    if(construct(G, i))
      printf("r_o(M_%d,P_%d)<=%d\n",K,N,i);
    else
      printf("r_o(M_%d,P_%d)>%d\n",K,N,i);
    printf("Positions analyzed so far: %d\n", (int)ANAL_POS.size());
  }
}
