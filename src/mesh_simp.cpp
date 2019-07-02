/*
* @Author: NanoApe
* @Date:   2019-06-25 21:11:52
* @Last Modified by:   NanoApe
* @Last Modified time: 2019-06-29 12:24:58
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

struct Pair { int u, v; double cost; Vec bestV; int tag; };
bool operator>(const Pair& a, const Pair& b) { return a.cost > b.cost; }
priority_queue<Pair, vector<Pair>, greater<Pair> > pairs;

int numV = 0, numT = 0;
Vec V[maxs_V];
int T[maxs_T][3];
int rmV = 0, rmT = 0;

set<int> triV[maxs_V];
set<int> verV[maxs_V];
double equaT[maxs_T][4];
double matrixT[maxs_T][4][4];
double matrixV[maxs_V][4][4];
bool disableV[maxs_V];
bool disableT[maxs_T];
int tag[maxs_V];

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
                fscanf(f, "%lf %lf %lf", &V[numV].x, &V[numV].y, &V[numV].z);
                numV++;
                break;
            case 'f':
                fscanf(f, "%d %d %d", &T[numT][0], &T[numT][1], &T[numT][2]);
                rep(i, 3) T[numT][i]--;
                numT++;
                break;
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
    rep(i, numV) if (disableV[i] == false) {
        total++;
        fprintf(f, "v %f %f %f\n", V[i].x, V[i].y, V[i].z);
        newID[i] = total;
    }
    rep(i, numT) if (disableT[i] == false)
        fprintf(f, "f %d %d %d\n", newID[T[i][0]], newID[T[i][1]], newID[T[i][2]]);

    fclose(f);
    printf("Vertex Number = %d\nTriangle Number = %d\n", numV-rmV, numT-rmT);
    printf("Writing to %s successfully\n", filename);
}

inline void getEquation(int o) {
    Vec& a=V[T[o][0]], b=V[T[o][1]], c=V[T[o][2]];
    equaT[o][0] = (b.y - a.y) * (c.z - a.z) - (c.y - a.y) * (b.z - a.z);
    equaT[o][1] = (b.z - a.z) * (c.x - a.x) - (c.z - a.z) * (b.x - a.x);
    equaT[o][2] = (b.x - a.x) * (c.y - a.y) - (c.x - a.x) * (b.y - a.y);
    double length = sqrt(sqr(equaT[o][0]) + sqr(equaT[o][1]) + sqr(equaT[o][2]));
    rep(i, 3) equaT[o][i] /= length;
    equaT[o][3] = - equaT[o][0] * a.x - equaT[o][1] * a.y - equaT[o][2] * a.z;
}

inline Pair getCost(int u, int v) {
    double Q[4][4];
    rep(i, 4) rep(j, 4) Q[i][j] = matrixV[u][i][j] + matrixV[v][i][j];

    // getMidPoint
    Vec bestV;
    double delta = Q[0][0] * Q[1][1] * Q[2][2] - Q[0][0] * Q[1][2] * Q[1][2] - Q[0][1] * Q[0][1] * Q[2][2]
                 + Q[0][1] * Q[1][2] * Q[0][2] + Q[0][2] * Q[0][1] * Q[1][2] - Q[0][2] * Q[1][1] * Q[0][2];
    if (delta > 1e-7) {
        double deltaX = Q[0][3] * Q[1][1] * Q[2][2] - Q[0][3] * Q[1][2] * Q[1][2] - Q[1][3] * Q[0][1] * Q[2][2]
                      + Q[1][3] * Q[1][2] * Q[0][2] + Q[2][3] * Q[0][1] * Q[1][2] - Q[2][3] * Q[1][1] * Q[0][2];
        double deltaY = Q[0][0] * Q[1][3] * Q[2][2] - Q[0][0] * Q[2][3] * Q[1][2] - Q[0][1] * Q[0][3] * Q[2][2]
                      + Q[0][1] * Q[2][3] * Q[0][2] + Q[0][2] * Q[0][3] * Q[1][2] - Q[0][2] * Q[1][3] * Q[0][2];
        double deltaZ = Q[0][0] * Q[1][1] * Q[2][3] - Q[0][0] * Q[1][2] * Q[1][3] - Q[0][1] * Q[0][1] * Q[2][3]
                      + Q[0][1] * Q[1][2] * Q[0][3] + Q[0][2] * Q[0][1] * Q[1][3] - Q[0][2] * Q[1][1] * Q[0][3];
        bestV = Vec(deltaX, deltaY, deltaZ) / (-delta);
    } else
        bestV = (V[u] + V[v]) / 2;

    double tmp[4];
    tmp[0] = bestV.x; tmp[1] = bestV.y; tmp[2] = bestV.z; tmp[3] = 1;

    double deltaV = 0;
    rep(i, 4) rep(j, 4) deltaV += tmp[j] * Q[j][i] * tmp[i];

    if (verV[u].size() != triV[u].size() || verV[v].size() != triV[v].size())
        deltaV += 10;

    return (Pair){u, v, deltaV, bestV, numV};
}

inline int insertT(int o) {
    rep(i, 3) T[numT][i] = T[o][i];
    getEquation(numT);
    rep(j, 4) rep(k, 4) matrixT[numT][j][k] = equaT[numT][j] * equaT[numT][k];
    rep(i, 3) triV[T[numT][i]].insert(numT);
    rep(i, 3) rep(j, 4) rep(k, 4) matrixV[T[numT][i]][j][k] += matrixT[numT][j][k];
    return numT++;
}

inline void removeV(int o) {
    if (disableV[o]) return;
    disableV[o] = true;
    traversal(set<int>, verV[o]) verV[*it].erase(o);
    rmV++;
}

inline void removeT(int o) {
    if (disableT[o]) return;
    disableT[o] = true;
    rep(i, 3) rep(j, 4) rep(k, 4) matrixV[T[o][i]][j][k] -= matrixT[o][j][k];
    rep(i, 3) triV[T[o][i]].erase(o);
    rmT++;
}

inline bool flip(int a, int b, Vec o) {
    Vec tmp;
    V[numV] = o;
    traversal(set<int>, triV[a]) {
        rep(i, 3) if (T[*it][i] == a && T[*it][(i+1)%3] != b && T[*it][(i+2)%3] != b) {
            T[*it][i] = numV;
            getEquation(*it);
            tmp = Vec(equaT[*it][0], equaT[*it][1], equaT[*it][2]);
            T[*it][i] = a;
            getEquation(*it);
            if (tmp.dot(Vec(equaT[*it][0], equaT[*it][1], equaT[*it][2])) < 0) return true;
        }
    }
    traversal(set<int>, triV[b]) {
        rep(i, 3) if (T[*it][i] == b && T[*it][(i+1)%3] != a && T[*it][(i+2)%3] != a) {
            T[*it][i] = numV;
            getEquation(*it);
            tmp = Vec(equaT[*it][0], equaT[*it][1], equaT[*it][2]);
            T[*it][i] = b;
            getEquation(*it);
            if (tmp.dot(Vec(equaT[*it][0], equaT[*it][1], equaT[*it][2])) < 0) return true;
        }
    }
    return false;
}

inline void deleteV() {
    Pair mn = pairs.top(); pairs.pop();
    while (disableV[mn.u] || disableV[mn.v] || tag[mn.u] > mn.tag || tag[mn.v] > mn.tag) {
        mn = pairs.top(); pairs.pop();
    }
    // if (mn.cost > 9) printf("%.12lf %d\n", mn.cost, numV - rmV);
    if (flip(mn.u, mn.v, mn.bestV)) return; // judge face flip
    int newV = numV++;
    V[newV] = mn.bestV;
    removeV(mn.u); removeV(mn.v);
    vector<int> needRemoveT;
    traversal(set<int>, triV[mn.u]) needRemoveT.push_back(*it);
    traversal(set<int>, triV[mn.v]) needRemoveT.push_back(*it);
    set<int> unionT;
    set_union(triV[mn.u].begin(), triV[mn.u].end(), triV[mn.v].begin(), triV[mn.v].end(),inserter(unionT, unionT.begin()));
    set<int> intersectionT;
    set_intersection(triV[mn.u].begin(), triV[mn.u].end(), triV[mn.v].begin(), triV[mn.v].end(),inserter(intersectionT, intersectionT.begin()));
    vector<int> needUpdateT;
    set_difference(unionT.begin(), unionT.end(), intersectionT.begin(), intersectionT.end(),inserter(needUpdateT, needUpdateT.begin()));
    set<int> needUpdateV;
    traversal(vector<int>, needRemoveT) removeT(*it);
    vector<int> newT;
    traversal(vector<int>, needUpdateT) rep(i, 3)
        if (T[*it][i] != mn.u && T[*it][i] != mn.v)
            needUpdateV.insert(T[*it][i]);
        else {
            int tmpV = T[*it][i];
            T[*it][i] = newV;
            newT.push_back(insertT(*it));
            T[*it][i] = tmpV;
        }
    traversal(set<int>, needUpdateV) tag[*it] = numV; tag[newV] = numV;
    traversal(set<int>, needUpdateV) {
        verV[*it].insert(newV);
        verV[newV].insert(*it);
    }
    traversal(set<int>, needUpdateV) pairs.push(getCost(*it, newV));
    traversal(vector<int>, newT) rep(i, 3)
        if (T[*it][i] == newV) {
            pairs.push(getCost(T[*it][(i+1)%3], T[*it][(i+2)%3]));
        }
    traversal(set<int>, needUpdateV)
        _traversal(set<int>, verV[*it])
            if (*_it != newV && needUpdateV.find(*_it) == needUpdateV.end())
                pairs.push(getCost(*it, *_it));
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

    rep(i, numT) rep(j, 3) triV[T[i][j]].insert(i);
    rep(i, numT) getEquation(i);
    rep(i, numT) rep(j, 3) rep(k, 2) verV[T[i][j]].insert(T[i][(j+k+1)%3]);
    rep(i, numT) rep(j, 4) rep(k, 4) matrixT[i][j][k] = equaT[i][j] * equaT[i][k];
    rep(i, numV) traversal(set<int>, triV[i]) rep(j, 4) rep(k, 4) matrixV[i][j][k] += matrixT[*it][j][k];
    rep(i, numT) rep(j, 3) pairs.push(getCost(T[i][j], T[i][(j+1)%3]));
    rep(i, numV) tag[i] = numV;

    int tmpT = numT;
    // int target = atof(argv[3]);
    // while (tmpV - (numV - rmV) < target) deleteV();
    double target = atof(argv[3]);
    while (1. * (numT - rmT) / tmpT > target) deleteV();

    printf("Used: %.3lf sec.\n", (double)(clock() - start) / CLOCKS_PER_SEC);

    save(argv[2]);
    return 0;
}