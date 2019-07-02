/*
* @Author: NanoApe
* @Date:   2019-06-25 21:11:52
* @Last Modified by:   NanoApe
* @Last Modified time: 2019-06-29 12:25:01
*/

#include <algorithm>
#include <iostream>
#include <assert.h>
#include <fstream>
#include <climits>
#include <cstring>
#include <limits>
#include <vector>
#include <cstdio>
#include <math.h>
#include <time.h>
#include <cmath>
#include <queue>
#include <list>
#include <set>
#include <map>

using namespace std;

#define maxs_V 1000000
#define maxs_T 1000000

#define rep(i, n) for(int i = 0; i < n; i++)
#define traversal(ty, nm) for(ty::iterator it = nm.begin(); it != nm.end(); ++it)
#define _traversal(ty, nm) for(ty::iterator _it = nm.begin(); _it != nm.end(); ++_it)
#define sqr(x) ((x)*(x))
#define mp make_pair

struct Edge;

struct Vert
{
    Vert(int _o, double _x, double _y, double _z, Edge* _e = NULL) : id(_o), x(_x), y(_y), z(_z), edge(_e) {}
    int id;
    double x, y, z;
    Edge* edge;  // one of the half-edges emantating from the vertex
    double matrix[4][4] = {{0}};
};

struct Face
{
    Face(Edge* _e = NULL) : edge(_e) {}
    Edge* edge;  // one of the half-edges bordering the face
    double equa[4] = {0};
    double matrix[4][4] = {{0}};
};

struct Edge
{
    Edge(Vert* _v = NULL, Edge* _p = NULL, Face* _f = NULL, Edge* _n = NULL) : vert(_v), pair(_p), face(_f), next(_n) {}
    Vert* vert;   // vertex at the end of the half-edge
    Edge* pair;   // oppositely oriented adjacent half-edge
    Face* face;   // face the half-edge borders
    Edge* next;   // next half-edge around the face
};

struct Vec {
    double x, y, z;
    Vec(double _x = 0, double _y = 0, double _z = 0) : x(_x), y(_y), z(_z) {}
    Vec operator+(const Vec& b) const { return Vec(x + b.x, y + b.y, z + b.z); }
    Vec &operator+=(const Vec &b) { x += b.x, y += b.y, z += b.z; return *this; }
    Vec operator-(const Vec& b) const { return Vec(x - b.x, y - b.y, z - b.z); }
    Vec &operator-=(const Vec &b) { x -= b.x, y -= b.y, z -= b.z; return *this; }
    Vec operator*(double b) const { return Vec(x * b, y * b, z * b); }
    Vec operator/(double b) const { return Vec(x / b, y / b, z / b); }
    Vec &operator/=(double b) { x /= b, y /= b, z /= b; return *this; }
    Vec mult(const Vec &b) const { return Vec(x * b.x, y * b.y, z * b.z); }
    double dot(const Vec &b) const { return x * b.x + y * b.y + z * b.z; }
    Vec cross(const Vec &b) const { return Vec(y * b.z - z * b.y, z * b.x - x * b.z, x * b.y - y * b.x); }
    Vec& norm() { return *this = *this * (1 / sqrt(x*x + y*y + z*z)); }
    double len() const { return sqrt(x*x + y*y + z*z); }
    double max() const { return (x>y && x>z) ? x : (y>z ? y : z); }
    double min() const { return (x<y && x<z) ? x : (y<z ? y : z); }
    void print() const { printf("%.12lf %.12lf %.12lf\n", x, y, z); }
};

struct Pair { int u, v; double cost; Vec bestV; int tag; Edge* edge; };
bool operator>(const Pair& a, const Pair& b) { return a.cost > b.cost; }
priority_queue<Pair, vector<Pair>, greater<Pair> > pairs;

int numV = 0, numT = 0;
int rmV = 0, rmT = 0;
Vert* V[maxs_V];
map<pair<int,int>,Edge*> Emap;
Edge* unpair[maxs_V];
int tag[maxs_V];

inline void getEquation(Face* f, Vert* a, Vert* b, Vert* c) {
    f->equa[0] = (b->y - a->y) * (c->z - a->z) - (c->y - a->y) * (b->z - a->z);
    f->equa[1] = (b->z - a->z) * (c->x - a->x) - (c->z - a->z) * (b->x - a->x);
    f->equa[2] = (b->x - a->x) * (c->y - a->y) - (c->x - a->x) * (b->y - a->y);
    double length = sqrt(sqr(f->equa[0]) + sqr(f->equa[1]) + sqr(f->equa[2]));
    rep(i, 3) f->equa[i] /= length;
    f->equa[3] = - f->equa[0] * a->x - f->equa[1] * a->y - f->equa[2] * a->z;
    rep(i, 4) rep(j, 4) f->matrix[i][j] = f->equa[i] * f->equa[j];
}

inline void load(const char* filename) {
    numV = numT = 0;
    FILE* f = fopen(filename, "r");
    char buf[256];
    while(fscanf(f, "%s", buf) != EOF) {
        switch (buf[0]) {
            case '#':
                fgets(buf, sizeof(buf), f);
                break;
            case 'v':
                double x, y, z;
                fscanf(f, "%lf %lf %lf", &x, &y, &z);
                V[numV] = new Vert(numV, x, y, z, NULL);
                numV++;
                break;
            case 'f': {
                int a, b, c;
                fscanf(f, "%d %d %d", &a, &b, &c); a--; b--; c--;
                Face* F = new Face(NULL);
                Edge* Ea = new Edge(V[b], NULL, F, NULL);
                Edge* Eb = new Edge(V[c], NULL, F, NULL);
                Edge* Ec = new Edge(V[a], NULL, F, NULL);
                F->edge = Ea;
                Ea->next = Eb;
                Eb->next = Ec;
                Ec->next = Ea;
                V[a]->edge = Ea;
                V[b]->edge = Eb;
                V[c]->edge = Ec;
                if (Emap.count(mp(a, b))) {
                    Ea->pair = Emap[mp(a, b)];
                    Ea->pair->pair = Ea;
                    Emap.erase(mp(a, b));
                } else Emap[mp(b, a)] = Ea;
                if (Emap.count(mp(b, c))) {
                    Eb->pair = Emap[mp(b, c)];
                    Eb->pair->pair = Eb;
                    Emap.erase(mp(b, c));
                } else Emap[mp(c, b)] = Eb;
                if (Emap.count(mp(c, a))) {
                    Ec->pair = Emap[mp(c, a)];
                    Ec->pair->pair = Ec;
                    Emap.erase(mp(c, a));
                } else Emap[mp(a, c)] = Ec;
                getEquation(F, V[a], V[b], V[c]);
                rep(i, 4) rep(j, 4) {
                    V[a]->matrix[i][j] += F->matrix[i][j];
                    V[b]->matrix[i][j] += F->matrix[i][j];
                    V[c]->matrix[i][j] += F->matrix[i][j];
                }
                numT++;
                break;
            }
            default:
                fgets(buf, sizeof(buf), f);
        }
    }
    fclose(f);
}

int newID[maxs_V];
inline void save(const char* filename) {
    FILE* f = fopen(filename, "w");

    fprintf(f, "# %d vertices %d triangles\n", numV-rmV, numT-rmT);
    int total = 0;
    rep(i, numV) if (V[i]) {
        fprintf(f, "v %f %f %f\n", V[i]->x, V[i]->y, V[i]->z);
        newID[V[i]->id] = ++total;
    }
    rep(i, numV) if (V[i]) {
        Edge* p = V[i]->edge; while (true) {
            if (V[i]->id == p->vert->id || p->vert->id == p->next->vert->id || p->vert->id == p->next->vert->id)
                printf("%d %d %d\n", V[i]->id, p->vert->id, p->next->vert->id);
            if (V[i]->id < p->vert->id && V[i]->id < p->next->vert->id)
                fprintf(f, "f %d %d %d\n", newID[V[i]->id], newID[p->vert->id], newID[p->next->vert->id]);
            if ((p = p->pair->next) == V[i]->edge) break;
        }
    }

    fclose(f);
    printf("Vertex Number = %d\nTriangle Number = %d\n", numV-rmV, numT-rmT);
    printf("Writing to %s successfully\n", filename);
}

inline Pair getCost(Vert* u, Vert* v, Edge* e) {
    double Q[4][4];
    rep(i, 4) rep(j, 4) Q[i][j] = u->matrix[i][j] + v->matrix[i][j];

    // getMidPoint
    Vec bestV;
    double delta = Q[0][0] * Q[1][1] * Q[2][2] - Q[0][0] * Q[1][2] * Q[1][2] - Q[0][1] * Q[0][1] * Q[2][2]
                 + Q[0][1] * Q[1][2] * Q[0][2] + Q[0][2] * Q[0][1] * Q[1][2] - Q[0][2] * Q[1][1] * Q[0][2];
    double deltaX, deltaY, deltaZ;
    if (delta > 1e-7) {
        deltaX = ( Q[0][3] * Q[1][1] * Q[2][2] - Q[0][3] * Q[1][2] * Q[1][2] - Q[1][3] * Q[0][1] * Q[2][2]
                 + Q[1][3] * Q[1][2] * Q[0][2] + Q[2][3] * Q[0][1] * Q[1][2] - Q[2][3] * Q[1][1] * Q[0][2] ) / (-delta);
        deltaY = ( Q[0][0] * Q[1][3] * Q[2][2] - Q[0][0] * Q[2][3] * Q[1][2] - Q[0][1] * Q[0][3] * Q[2][2]
                 + Q[0][1] * Q[2][3] * Q[0][2] + Q[0][2] * Q[0][3] * Q[1][2] - Q[0][2] * Q[1][3] * Q[0][2] ) / (-delta);
        deltaZ = ( Q[0][0] * Q[1][1] * Q[2][3] - Q[0][0] * Q[1][2] * Q[1][3] - Q[0][1] * Q[0][1] * Q[2][3]
                 + Q[0][1] * Q[1][2] * Q[0][3] + Q[0][2] * Q[0][1] * Q[1][3] - Q[0][2] * Q[1][1] * Q[0][3] ) / (-delta);
    } else {
        deltaX = (u->x + v->x) / 2;
        deltaY = (u->y + v->y) / 2;
        deltaZ = (u->z + v->z) / 2;
    }
    bestV = Vec(deltaX, deltaY, deltaZ);

    double tmp[4];
    tmp[0] = bestV.x; tmp[1] = bestV.y; tmp[2] = bestV.z; tmp[3] = 1;

    double deltaV = 0;
    rep(i, 4) rep(j, 4) deltaV += tmp[j] * Q[j][i] * tmp[i];

    return (Pair){u->id, v->id, deltaV, bestV, numV, e};
}

inline double dot(double* a, double* b) {
    double sum = 0;
    rep(i, 3) sum += a[i] * b[i];
    return sum;
}

int col[maxs_V], _col;
inline bool flip(Pair& mn) {
    Vert* c = new Vert(-1, mn.bestV.x, mn.bestV.y, mn.bestV.z);
    Face* tmp = new Face();

    _col++;
    int count = 0;
    Edge* e = mn.edge;
    while ((e = e->pair->next) != mn.edge)
        if (col[e->vert->id] == _col)
            count++;
        else
            col[e->vert->id] = _col;
    e = e->pair;
    while ((e = e->pair->next) != mn.edge->pair)
        if (col[e->vert->id] == _col)
            count++;
        else
            col[e->vert->id] = _col;

    if (count > 2) return true;

    e = mn.edge;
    while (true) {
        Edge* p = e->pair->next; while ((p = p->pair->next) != e) {
            getEquation(tmp, V[p->vert->id], V[p->next->vert->id], c);
            if (dot(tmp->equa, p->face->equa) < 0) return true;
        }
        if ((e = e->pair) == mn.edge) break;
    }

    delete c;
    delete tmp;
    return false;
}

inline void subMatrix(Face *f) {
    rep(i, 4) rep(j, 4) {
        f->edge->vert->matrix[i][j] -= f->matrix[i][j];
        f->edge->next->vert->matrix[i][j] -= f->matrix[i][j];
        f->edge->next->next->vert->matrix[i][j] -= f->matrix[i][j];
    }
}

inline void deleteV() {
    Pair mn = pairs.top(); pairs.pop();
    while (V[mn.u] == NULL || V[mn.v] == NULL || tag[mn.u] > mn.tag || tag[mn.v] > mn.tag) {
        mn = pairs.top(); pairs.pop();
    }
    // if (mn.cost > 9) printf("%.12lf %d\n", mn.cost, numV - rmV);
    if (flip(mn)) return;
    int newV = numV++;
    V[newV] = new Vert(newV, mn.bestV.x, mn.bestV.y, mn.bestV.z);

    Edge* e = mn.edge; int a, b, c;
    while (true) {
        Edge* p = e->pair->next; while ((p = p->pair->next) != e) {
            Face* F = new Face(NULL);
            Edge* Ea = new Edge(p->vert, NULL, F, NULL);
            Edge* Eb = new Edge(p->next->vert, NULL, F, NULL);
            Edge* Ec = new Edge(V[newV], NULL, F, NULL);
            F->edge = Ea;
            Ea->next = Eb;
            Eb->next = Ec;
            Ec->next = Ea;
            V[ a = newV ]->edge = Ea;
            V[ b = p->vert->id ]->edge = Eb;
            V[ c = p->next->vert->id ]->edge = Ec;
            if (unpair[b]) {
                Ea->pair = unpair[b];
                Ea->pair->pair = Ea;
                unpair[b] = NULL;
            } else unpair[b] = Ea;
            Eb->pair = p->next->pair;
            Eb->pair->pair = Eb;
            if (unpair[c]) {
                Ec->pair = unpair[c];
                Ec->pair->pair = Ec;
                unpair[c] = NULL;
            } else unpair[c] = Ec;
            getEquation(F, V[a], V[b], V[c]);
            rep(i, 4) rep(j, 4) {
                V[a]->matrix[i][j] += F->matrix[i][j];
                V[b]->matrix[i][j] += F->matrix[i][j];
                V[c]->matrix[i][j] += F->matrix[i][j];
            }
            numT++;
        }
        if ((e = e->pair) == mn.edge) break;
    }
    while (true) {
        Edge* p = e->pair->next;
        while ((p = p->pair->next) != e) {
            if (p->next->next->pair->next->vert != e->vert)
                delete p->next->next->pair;
            subMatrix(p->face); rmT++;
            delete p->face;
            delete p->next->next;
            delete p->next;
        }
        delete p->next->next->pair;
        if ((e = e->pair) == mn.edge) break;
    }
    subMatrix(e->pair->face); rmT++;
    delete e->pair->face;
    delete e->pair->next->next;
    delete e->pair->next;
    delete e->pair;
    subMatrix(e->face); rmT++;
    delete e->face;
    delete e->next->next;
    delete e->next;
    delete e;

    V[mn.u] = V[mn.v] = NULL;
    rmV += 2;

    tag[newV] = numV;
    e = V[newV]->edge; while (true) {
        tag[e->vert->id] = numV;
        Edge* p = e->pair; while (p->pair->next->vert->id != newV) {
            pairs.push(getCost(e->vert, p->vert, p));
            p = p->pair->next;
        }
        if ((e = e->pair->next) == V[newV]->edge) break;
    }
}

int main(int argc, char **argv) {

    clock_t start = clock();

    if (argc != 4) {
        cout << "Usage: " << argv[0] << " <input obj file> <output obj file> <simplification ratio>" << endl;
        return 0;
    }

    load(argv[1]);

    printf("Loading from %s successfully.\n", argv[1]);
    printf("Vertex Number = %d\n", numV);
    printf("Triangle Number = %d\n", numT);

    rep(i, numV) {
        tag[i] = numV;
        Edge* p = V[i]->edge; while (true) {
            if (p->vert->id < i)
                pairs.push(getCost(V[i], p->vert, p));
            if ((p = p->pair->next) == V[i]->edge) break;
        }
    }

    int tmpT = numT;
    // int target = atof(argv[3]);
    // while (tmpV - (numV - rmV) < target) deleteV();
    double target = atof(argv[3]);
    while (1. * (numT - rmT) / tmpT > target) deleteV();

    printf("Used: %.3lf sec.\n", (double)(clock() - start) / CLOCKS_PER_SEC);

    save(argv[2]);
    return 0;
}