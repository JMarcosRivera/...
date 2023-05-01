#include<bits/stdc++.h>
#include<ext/pb_ds/assoc_container.hpp>
#include<ext/pb_ds/tree_policy.hpp>
#define db(x) cerr << #x << ": " << (x) << '\n'
#define maxn 2000
#define pb push_back
#define f first
#define X real()
#define Y imag()
#define mp make_pair
#define int long long
#define log2(n) (31-__builtin_clz(n))
#define less(n) order_of_key(n)
#define en_pos(n) find_by_order(n)
#define x1 first
#define y1 second
#define s second
#define frb(i,a,b) for(ll (i)=(a);(i) <= (b); (i)+=(i)&-(i))
#define rfrb(i,a) for(ll (i)=(a);(i) > 0;(i)-=(i)&-(i))
#define fr(i,a,b) for(ll (i) = (a); (i) <= (b); (i)++)
#define rep(i,c) for(auto (i) : (c))
#define mini(a,b) (((a) < (b)) ? (a) : (b))
#define maxi(a,b) (((a) > (b)) ? (a) : (b))
#define vp vector<par>
#define vi vector<ll>
#define dq deque<ll>
#define mem(i,j) memset((i),(j),sizeof (i))
#define unic(v) v.resize(unique(v.begin(),v.end())-v.begin())
#define all(s) s.begin(),s.end()
/// --- >> iterador --- >> empieza en 0

using namespace __gnu_pbds;
using namespace std;
template <typename T>
using ordered_set = tree<T, null_type, less<T>, rb_tree_tag, tree_order_statistics_node_update>;
typedef long long ll;
typedef unsigned long long ull;
typedef pair<ll,ll>par;
typedef long double ld;
typedef complex<ld> P;
const ld eps = 1e-9;
const ld pi = acos(-1);
const ll mod = 998244353;
const ll mod2 = 998244353;
const ll Max = mod * mod;
const double PI = acos((double)-1.0);
int sign(double x) { return (x > eps) - (x < -eps); }


const int sqr = 435;
inline ld degree(ld radians){
    ld ans = (radians*(ld)180)/pi;
    return ans;
}
inline ld radians(ld deg){
    ld ans = (pi*deg)/(ld)180;
    return ans;
}
ull modmul(ull a, ull b, ull M) {
	ll ret = a * b - M * ull(1.L / M * a * b);
	return ret + M * (ret < 0) - M * (ret >= (ll)M);
}
int gcd(int a,int b){
    if(b == 0)return b;
    return gcd(b,a%b);
}
int pot(int x,int n){
    if(n == 0){
        return 1;
    }
    if(n == 1)return x;
    int mid = pot(x,n/2);
    mid *= mid;
    mid %= mod;
    if(n%2 == 1)mid = (mid * x) % mod;
    return mid;
}
/// Prime Numbers:
/// 2, 173, 179, 181, 197, 311, 331, 737, 1009, 2011, 2027, 3079, 4001, 10037, 10079, 20011, 20089;
/// 100003, 100019, 100043, 200003, 200017, 1000003, 1000033, 1000037, 1000081;
/// 2000003, 2000029, 2000039, 1000000007, 1000000021, 2000000099;



mt19937 rng(chrono::high_resolution_clock::now().time_since_epoch().count());
template<typename T>
static T randint(T lo, T hi) { return uniform_int_distribution<T>(lo, hi)(rng); }

vector<pair<int,int>>g[maxn];
int mk[maxn];

using T = long long;
const T inf = 1LL << 61;
const int N = 510;

struct Min_Cost_Max_Flow {
  struct edge {
    int u, v;
    T cap, cost;
    int id;
    edge(int _u, int _v, T _cap, T _cost, int _id) {
      u = _u;
      v = _v;
      cap = _cap;
      cost = _cost;
      id = _id;
    }
  };
  int n, s, t, mxid;
  T flow, cost;
  vector<vector<int>> g;
  vector<edge> e;
  vector<T> d, potential, flow_through;
  vector<int> par;
  bool neg;
  Min_Cost_Max_Flow() {}
  Min_Cost_Max_Flow(int _n) { // 0-based indexing
    n = _n + 10;
    g.assign(n, vector<int> ());
    neg = false;
    mxid = 0;
  }
  void add_edge(int u, int v, T cap, T cost, int id = -1, bool directed = true) {
    if(cost < 0) neg = true;
    g[u].push_back(e.size());
    e.push_back(edge(u, v, cap, cost, id));
    g[v].push_back(e.size());
    e.push_back(edge(v, u, 0, -cost, -1));
    mxid = max(mxid, id);
    if(!directed) add_edge(v, u, cap, cost, id + N, true); // tracks the reverse edges for undirected graphs
  }
  bool dijkstra() {
    par.assign(n, -1);
    d.assign(n, inf);
    priority_queue<pair<T, T>, vector<pair<T, T>>, greater<pair<T, T>> > q;
    d[s] = 0;
    q.push(pair<T, T>(0, s));
    while (!q.empty()) {
      int u = q.top().second;
      T nw = q.top().first;
      q.pop();
      if(nw != d[u]) continue;
      for (int i = 0; i < (int)g[u].size(); i++) {
        int id = g[u][i];
        int v = e[id].v;
        T cap = e[id].cap;
        T w = e[id].cost + potential[u] - potential[v];
        if (d[u] + w < d[v] && cap > 0) {
          d[v] = d[u] + w;
          par[v] = id;
          q.push(pair<T, T>(d[v], v));
        }
      }
    }
    for (int i = 0; i < n; i++) { // update potential
      if(d[i] < inf) potential[i] += d[i];
    }
    return d[t] != inf;
  }
  T send_flow(int v, T cur) {
    if(par[v] == -1) return cur;
    int id = par[v];
    int u = e[id].u;
    T w = e[id].cost;
    T f = send_flow(u, min(cur, e[id].cap));
    cost += f * w;
    e[id].cap -= f;
    e[id ^ 1].cap += f;
    return f;
  }
  //returns {maxflow, mincost}
  pair<T, T> solve(int _s, int _t, T goal = inf) {
    s = _s;
    t = _t;
    flow = 0, cost = 0;
    potential.assign(n, 0);
    if (neg) {
      // run Bellman-Ford to find starting potential
      d.assign(n, inf);
      for (int i = 0, relax = true; i < n && relax; i++) {
        for (int u = 0; u < n; u++) {
          for (int k = 0; k < (int)g[u].size(); k++) {
            int id = g[u][k];
            int v = e[id].v;
            T cap = e[id].cap, w = e[id].cost;
            if (d[v] > d[u] + w && cap > 0) {
              d[v] = d[u] + w;
              relax = true;
            }
          }
        }
      }
      for(int i = 0; i < n; i++) if(d[i] < inf) potential[i] = d[i];
    }
    while (flow < goal && dijkstra()) flow += send_flow(t, goal - flow);
    flow_through.assign(mxid + 10, 0);
    for (int u = 0; u < n; u++) {
      for (auto v : g[u]) {
        if (e[v].id >= 0) flow_through[e[v].id] = e[v ^ 1].cap;
      }
    }
    return make_pair(flow, cost);
  }
};

int n;

vector<int> bfs(int u){
    queue<int>q;
    vector<int>flag(n+1,0);
    vector<int>p(n+1,0),e(n+1,0);

    q.push(u);
    flag[u] = 1;

    while(!q.empty()){
        u = q.front();
        q.pop();

        int v,next_edge;
        for(auto i : g[u]){
            v = i.f;
            next_edge = i.s;
            if(!flag[v] && !mk[next_edge]){
                flag[v] = 1;
                e[v] = next_edge;
                q.push(v);
                p[v] = u;
            }
        }
    }

    u = n;
    vector<int>cur;

    while(1){
        cur.pb(u);
        if(u == 1)break;
        mk[e[u]] = 1;
        u = p[u];
    }
    reverse(cur.begin(),cur.end());
    return cur;
}
main(){
    ios_base::sync_with_stdio(0);
    cin.tie(0);

    int m;
    cin >> n >> m;

    Min_Cost_Max_Flow my_flow = Min_Cost_Max_Flow(n+2);


    set<par>initial_edges;

    my_flow.add_edge(0,1,n,0);
    my_flow.add_edge(n,n+1,n,0);

    vector<par>edges;
    for(int i=1;i<=m;i++){
        int a,b;
        cin >> a >> b;
        my_flow.add_edge(a,b,1,0,i); ///inicio fin flujo costo indice_arista
        edges.push_back({a,b});
    }


    int flow = my_flow.solve(0,n+1).f;

    int cn = 0;

    for(int i=1;i<=m;i++){
        if(my_flow.flow_through[i] > 0){  ///the edge with index i is on the flow 
            g[edges[i-1].f].pb({edges[i-1].s,++cn});
        }
    }


     cout << flow << '\n';
     while(flow--){
        vector<int>cur = bfs(1);
        cout << cur.size() << '\n';
        for(auto i : cur){
            cout << i << " ";
        }
        cout<< '\n';

    }

}


