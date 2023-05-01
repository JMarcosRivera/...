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

struct FlowEdge {
    int v, u;
    long long cap, flow = 0;
    FlowEdge(int v, int u, long long cap) : v(v), u(u), cap(cap) {}
};

vector<pair<int,int>>g[maxn];
int mk[maxn];

struct Dinic {
    const long long flow_inf = 1e18;
    vector<FlowEdge> edges;
    vector<vector<int>> adj;
    int n, m = 0;
    int s, t;
    vector<int> level, ptr;
    queue<int> q;

    Dinic(int n, int s, int t) : n(n), s(s), t(t) {
        adj.resize(n);
        level.resize(n);
        ptr.resize(n);
    }

    void add_edge(int v, int u, long long cap) {
        edges.emplace_back(v, u, cap);
        edges.emplace_back(u, v, 0);
        adj[v].push_back(m);
        adj[u].push_back(m + 1);
        m += 2;
    }

    bool bfs() {
        while (!q.empty()) {
            int v = q.front();
            q.pop();
            for (int id : adj[v]) {
                if (edges[id].cap - edges[id].flow < 1)
                    continue;
                if (level[edges[id].u] != -1)
                    continue;
                level[edges[id].u] = level[v] + 1;
                q.push(edges[id].u);
            }
        }
        return level[t] != -1;
    }

    long long dfs(int v, long long pushed) {
        if (pushed == 0)
            return 0;
        if (v == t)
            return pushed;
        for (int& cid = ptr[v]; cid < (int)adj[v].size(); cid++) {
            int id = adj[v][cid];
            int u = edges[id].u;
            if (level[v] + 1 != level[u] || edges[id].cap - edges[id].flow < 1)
                continue;
            long long tr = dfs(u, min(pushed, edges[id].cap - edges[id].flow));
            if (tr == 0)
                continue;
            edges[id].flow += tr;
            edges[id ^ 1].flow -= tr;
            return tr;
        }
        return 0;
    }

    long long flow() {
        long long f = 0;
        while (true) {
            fill(level.begin(), level.end(), -1);
            level[s] = 0;
            q.push(s);
            if (!bfs())
                break;
            fill(ptr.begin(), ptr.end(), 0);
            while (long long pushed = dfs(s, flow_inf)) {
                f += pushed;
            }
        }
        return f;
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
    cout.tie(0);


    int m;
    cin >> n >> m;

    Dinic my_flow = Dinic(n+2,0,n+1);

    my_flow.add_edge(0,1,n);
    my_flow.add_edge(n,n+1,n);

    set<par>initial_edges;

    for(int i=1;i<=m;i++){
        int a,b;
        cin >> a >> b;
        my_flow.add_edge(a,b,1);
        initial_edges.insert({a,b});
    }

    vector<par>edges;
    int flow = my_flow.flow();

    int cn = 0;
    for(auto i : my_flow.edges){
        int u = i.v;
        int v = i.u;
        int flow = i.flow;
        if(flow >= 0)continue;
        if(v >= 1 && v <= n && u >= 1 && u <= n ){
            cn++;
            g[v].push_back({u,cn}); ///edge v --> u detected in the flow network

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
