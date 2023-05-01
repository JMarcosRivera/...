#include <bits/stdc++.h>
 
using namespace std;
 
#define maxn 550
#define pb push_back
#define int long long
#define all(x) (x).begin(), (x).end()
 
int mat[maxn][maxn];
const int inf = 1e18;
 
template<typename T>
T min_assignment(const vector<vector<T>> &c) {
    const int n = c.size(), m = c[0].size(); // assert(n <= m);
    vector<T> v(m), dist(m); // v: potential
    vector<int> matchL(n, -1), matchR(m, -1); // matching pairs
    vector<int> index(m), prev(m);
 
    iota(all(index), 0);
 
    auto residue = [&](int i, int j) {
        return c[i][j] - v[j];
    };
 
    for(int f = 0; f < n; ++f) {
        for(int j = 0; j < m; ++j) {
            dist[j] = residue(f, j);
            prev[j] = f;
        }
        T w;
        int j, l;
        for(int s = 0, t = 0;;) {
            if(s == t) {
                l = s;
                w = dist[index[t++]];
                for(int k = t; k < m; ++k) {
                    j = index[k];
                    T h = dist[j];
                    if(h <= w) {
                        if(h < w) {
                            t = s;
                            w = h;
                        }
                        index[k] = index[t];
                        index[t++] = j;
                    }
                }
                for(int k = s; k < t; ++k) {
                    j = index[k];
                    if(matchR[j] < 0)
                        goto aug;
                }
            }
            int q = index[s++], i = matchR[q];
            for(int k = t; k < m; ++k) {
                j = index[k];
                T h = residue(i, j) - residue(i, q) + w;
                if(h < dist[j]) {
                    dist[j] = h;
                    prev[j] = i;
                    if(h == w) {
                        if(matchR[j] < 0)
                            goto aug;
                        index[k] = index[t];
                        index[t++] = j;
                    }
                }
            }
        }
aug:
        for(int k = 0; k < l; ++k)
            v[index[k]] += dist[index[k]] - w;
        int i;
        do {
            matchR[j] = i = prev[j];
            swap(j, matchL[i]);
        } while(i != f);
    }
    T opt = 0;
    for(int i = 0; i < n; ++i)
        opt += c[i][matchL[i]]; // (i, matchL[i]) is a solution
    return opt;
}
 
main()
{
    ios_base::sync_with_stdio(0);
    cin.tie(0);
 
    int n;
    cin >> n;
 
    int sz = n + 2;
    if(n % 2 == 1){
        sz++;
    }
 
    vector <vector <int>> v(n/2 + n%2, vector <int> (n/2 + n%2, 0));
 
    for(int i=1;i<=n;i++){
        for(int j=1;j<=n;j++){
            cin >> mat[i][j];
        }
    }
 
    if(n % 2 == 1)n++;
 
    for(int i=2;i<=n;i+=2){
        for(int j=1;j<n;j+=2){
            int cost = mat[j][i] + mat[j][i-2];
            v[(j-1)/2][(i/2)-1] = cost;
            //cout << j << " " << i << " " << cost << '\n';
        }
 
    }
 
 
    cout << min_assignment<int>(v);
 
 
 
 
 
}
