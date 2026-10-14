#define _POSIX_C_SOURCE 200809L
#include <stdio.h>
#include <stdlib.h>
#include <time.h>

#define VERTICES 50
#define SPARSE_EDGES 100
#define DENSE_EDGES 600
#define INF 1000000000
#define REPEAT 2000   /* 4개 케이스 모두 동일: 2000회 반복 평균 */

typedef struct { int u, v, weight; } Edge;
typedef struct Node { int vertex, weight; struct Node *next; } Node;
typedef Node *AdjList[VERTICES];
typedef int AdjMatrix[VERTICES][VERTICES];

/* ================= 그래프 생성 ================= */
int edgeExists(Edge edges[], int edgeCount, int u, int v) {
    for (int i = 0; i < edgeCount; i++)
        if ((edges[i].u == u && edges[i].v == v) || (edges[i].u == v && edges[i].v == u))
            return 1;
    return 0;
}

void addEdge(Edge edges[], int *edgeCount, int u, int v) {
    edges[*edgeCount].u = u;
    edges[*edgeCount].v = v;
    edges[*edgeCount].weight = rand() % 100 + 1;
    (*edgeCount)++;
}

void generateGraph(Edge edges[], int targetEdges) {
    int edgeCount = 0;
    for (int v = 1; v < VERTICES; v++)           /* 연결성 보장 */
        addEdge(edges, &edgeCount, rand() % v, v);
    while (edgeCount < targetEdges) {
        int u = rand() % VERTICES, v = rand() % VERTICES;
        if (u == v || edgeExists(edges, edgeCount, u, v)) continue;
        addEdge(edges, &edgeCount, u, v);
    }
}

/* 연결 그래프 확인 (DFS) */
int isConnected(Edge edges[], int edgeCount) {
    int adj[VERTICES][VERTICES] = {{0}}, seen[VERTICES] = {0}, stack[VERTICES], sp = 0, cnt = 0;
    for (int i = 0; i < edgeCount; i++)
        adj[edges[i].u][edges[i].v] = adj[edges[i].v][edges[i].u] = 1;
    stack[sp++] = 0; seen[0] = 1;
    while (sp) {
        int x = stack[--sp]; cnt++;
        for (int y = 0; y < VERTICES; y++)
            if (adj[x][y] && !seen[y]) { seen[y] = 1; stack[sp++] = y; }
    }
    return cnt == VERTICES;
}

/* 단순 그래프 + 연결 그래프 검사 (자기 루프, 중복 간선, 연결성) */
int validateGraph(Edge edges[], int edgeCount) {
    for (int i = 0; i < edgeCount; i++) {
        if (edges[i].u == edges[i].v || edges[i].weight <= 0) return 0;
        for (int j = i + 1; j < edgeCount; j++)
            if ((edges[i].u == edges[j].u && edges[i].v == edges[j].v) ||
                (edges[i].u == edges[j].v && edges[i].v == edges[j].u)) return 0;
    }
    return isConnected(edges, edgeCount);
}

/* ================= 그래프 표현 ================= */
void initMatrix(AdjMatrix m) {
    for (int i = 0; i < VERTICES; i++)
        for (int j = 0; j < VERTICES; j++) m[i][j] = (i == j) ? 0 : INF;
}
void initList(AdjList list) { for (int i = 0; i < VERTICES; i++) list[i] = NULL; }

void addListEdge(AdjList list, int u, int v, int weight) {
    Node *n = malloc(sizeof(Node));
    if (!n) { printf("Memory allocation failed!\n"); exit(EXIT_FAILURE); }
    n->vertex = v; n->weight = weight; n->next = list[u]; list[u] = n;
}
void addMatrixEdge(AdjMatrix m, int u, int v, int w) { m[u][v] = w; m[v][u] = w; }

void buildRepresentations(Edge edges[], int edgeCount, AdjList list, AdjMatrix matrix) {
    initList(list); initMatrix(matrix);
    for (int i = 0; i < edgeCount; i++) {
        addListEdge(list, edges[i].u, edges[i].v, edges[i].weight);
        addListEdge(list, edges[i].v, edges[i].u, edges[i].weight);
        addMatrixEdge(matrix, edges[i].u, edges[i].v, edges[i].weight);
    }
}

void freeList(AdjList list) {
    for (int i = 0; i < VERTICES; i++) {
        Node *p = list[i];
        while (p) { Node *n = p->next; free(p); p = n; }
        list[i] = NULL;
    }
}

/* ================= Kruskal (인접 리스트) ================= */
int compareEdges(const void *a, const void *b) {
    return ((const Edge *)a)->weight - ((const Edge *)b)->weight;
}
int findSet(int parent[], int x) {
    if (parent[x] != x) parent[x] = findSet(parent, parent[x]);
    return parent[x];
}
int unionSets(int parent[], int a, int b) {
    int ra = findSet(parent, a), rb = findSet(parent, b);
    if (ra == rb) return 0;
    parent[rb] = ra;
    return 1;
}

int kruskalFromList(AdjList list, Edge mst[], int *totalCost) {
    Edge edges[DENSE_EDGES];
    int edgeCount = 0, parent[VERTICES], mstCount = 0;

    for (int u = 0; u < VERTICES; u++)                /* 리스트에서 간선 수집 (무방향이므로 u<v만) */
        for (Node *c = list[u]; c; c = c->next)
            if (u < c->vertex) {
                edges[edgeCount].u = u;
                edges[edgeCount].v = c->vertex;
                edges[edgeCount].weight = c->weight;
                edgeCount++;
            }

    *totalCost = 0;
    for (int i = 0; i < VERTICES; i++) parent[i] = i;
    qsort(edges, edgeCount, sizeof(Edge), compareEdges);

    for (int i = 0; i < edgeCount; i++)
        if (unionSets(parent, edges[i].u, edges[i].v)) {
            mst[mstCount++] = edges[i];
            *totalCost += edges[i].weight;
            if (mstCount == VERTICES - 1) break;
        }
    return mstCount;
}

/* ================= Prim (인접 행렬, key[] 배열 방식 O(V^2)) ================= */
int prim(AdjMatrix matrix, Edge mst[], int *totalCost) {
    int key[VERTICES], parent[VERTICES], visited[VERTICES];
    int mstCount = 0;
    *totalCost = 0;
    for (int i = 0; i < VERTICES; i++) { key[i] = INF; parent[i] = -1; visited[i] = 0; }
    key[0] = 0;                                        /* 시작 정점 0 */

    for (int it = 0; it < VERTICES; it++) {
        int u = -1;
        for (int i = 0; i < VERTICES; i++)             /* key가 가장 작은 미방문 정점 선택 */
            if (!visited[i] && (u == -1 || key[i] < key[u])) u = i;
        if (u == -1 || key[u] >= INF) break;
        visited[u] = 1;
        if (parent[u] != -1) {
            mst[mstCount].u = parent[u];
            mst[mstCount].v = u;
            mst[mstCount].weight = key[u];
            mstCount++;
            *totalCost += key[u];
        }
        for (int v = 0; v < VERTICES; v++)             /* key 갱신 */
            if (!visited[v] && matrix[u][v] < key[v]) { key[v] = matrix[u][v]; parent[v] = u; }
    }
    return mstCount;
}

/* ================= 메모리 계산 (Byte) ================= */
size_t listMemoryBytes(int edgeCount) {
    return sizeof(AdjList) + (size_t)edgeCount * 2 * sizeof(Node);
}
/* 리스트 + 간선 배열 + parent[] (Union-Find) + MST 결과 배열 */
size_t kruskalMemoryBytes(int edgeCount) {
    return listMemoryBytes(edgeCount)
         + (size_t)edgeCount * sizeof(Edge)
         + sizeof(int) * VERTICES
         + sizeof(Edge) * (VERTICES - 1);
}
/* 행렬 + key[] + parent[] + visited[] + MST 결과 배열 */
size_t primMemoryBytes(void) {
    return sizeof(AdjMatrix)
         + 3 * sizeof(int) * VERTICES
         + sizeof(Edge) * (VERTICES - 1);
}

/* ================= 시간 측정 (모든 케이스 동일 방법) ================= */
double nowMs(void) {
    struct timespec t;
    clock_gettime(CLOCK_MONOTONIC, &t);
    return t.tv_sec * 1000.0 + t.tv_nsec / 1e6;
}
double measureKruskalMs(AdjList list, Edge mst[], int *cost, int *cnt) {
    double s = nowMs();
    for (int i = 0; i < REPEAT; i++) *cnt = kruskalFromList(list, mst, cost);
    return (nowMs() - s) / REPEAT;
}
double measurePrimMs(AdjMatrix m, Edge mst[], int *cost, int *cnt) {
    double s = nowMs();
    for (int i = 0; i < REPEAT; i++) *cnt = prim(m, mst, cost);
    return (nowMs() - s) / REPEAT;
}

/* ================= 출력 ================= */
void printCase(int no, const char *title, int edges, int mstCount,
               int cost, size_t mem, double ms, Edge mst[]) {
    printf("Case %d : %s\n", no, title);
    printf("Vertices      : %d\n", VERTICES);
    printf("Edges         : %d\n", edges);
    printf("MST Edges     : %d\n", mstCount);
    printf("MST Cost      : %d\n", cost);
    printf("Memory        : %zu Bytes\n", mem);
    printf("Execution Time: %.6f ms\n", ms);
    printf("MST Edge List :\n");
    for (int i = 0; i < mstCount; i++)
        printf("  %2d -- %2d (weight: %3d)\n", mst[i].u, mst[i].v, mst[i].weight);
    printf("\n");
}

int main(void) {
    srand((unsigned int)time(NULL));

    Edge sparseEdges[SPARSE_EDGES], denseEdges[DENSE_EDGES];
    AdjList sparseList, denseList;
    AdjMatrix sparseMatrix, denseMatrix;

    /* 연결 그래프가 나올 때까지 재생성 */
    do { generateGraph(sparseEdges, SPARSE_EDGES); } while (!validateGraph(sparseEdges, SPARSE_EDGES));
    do { generateGraph(denseEdges, DENSE_EDGES); } while (!validateGraph(denseEdges, DENSE_EDGES));
    printf("Graph check: Sparse = Connected/Simple, Dense = Connected/Simple\n\n");

    buildRepresentations(sparseEdges, SPARSE_EDGES, sparseList, sparseMatrix);
    buildRepresentations(denseEdges, DENSE_EDGES, denseList, denseMatrix);

    Edge m1[VERTICES - 1], m2[VERTICES - 1], m3[VERTICES - 1], m4[VERTICES - 1];
    int c1, c2, c3, c4, n1, n2, n3, n4;

    double t1 = measureKruskalMs(sparseList, m1, &c1, &n1);
    double t2 = measureKruskalMs(denseList, m2, &c2, &n2);
    double t3 = measurePrimMs(sparseMatrix, m3, &c3, &n3);
    double t4 = measurePrimMs(denseMatrix, m4, &c4, &n4);

    printCase(1, "Sparse Graph - Adjacency List - Kruskal", SPARSE_EDGES, n1, c1, kruskalMemoryBytes(SPARSE_EDGES), t1, m1);
    printCase(2, "Dense Graph - Adjacency List - Kruskal", DENSE_EDGES, n2, c2, kruskalMemoryBytes(DENSE_EDGES), t2, m2);
    printCase(3, "Sparse Graph - Adjacency Matrix - Prim", SPARSE_EDGES, n3, c3, primMemoryBytes(), t3, m3);
    printCase(4, "Dense Graph - Adjacency Matrix - Prim", DENSE_EDGES, n4, c4, primMemoryBytes(), t4, m4);

    printf("[Verify] Sparse: Kruskal %d vs Prim %d -> %s\n", c1, c3, c1 == c3 ? "SAME" : "DIFFERENT");
    printf("[Verify] Dense : Kruskal %d vs Prim %d -> %s\n", c2, c4, c2 == c4 ? "SAME" : "DIFFERENT");

    freeList(sparseList);
    freeList(denseList);
    return 0;
}