#include<bits/stdc++.h>
#include<ext/pb_ds/assoc_container.hpp>
#include<ext/pb_ds/tree_policy.hpp>
#define int long long
#define db(x) cerr << #x << ": " << (x) << '\n'
#define maxn 1010000
#define pb push_back
#define f first
#define s second
#define X real()
#define Y imag()
#define mp make_pair
#define log2(n) (31-__builtin_clz(n))
#define less(n) order_of_key(n)
#define en_pos(n) find_by_order(n)
#define x1 first
#define y1 second
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
const ll mod = 1000000007;
const ll mod2 = 998244353;
const ll Max = mod * mod;
const ll Min = -Max;
const double PI = acos((double)-1.0);
int sign(double x) { return (x > eps) - (x < -eps); }


const int sqr = 350;
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
}
/// Prime Numbers:
/// 2, 173, 179, 181, 197, 311, 331, 737, 1009, 2011, 2027, 3079, 4001, 10037, 10079, 20011, 20089;
/// 100003, 100019, 100043, 200003, 200017, 1000003, 1000033, 1000037, 1000081;
/// 2000003, 2000029, 2000039, 1000000007, 1000000021, 2000000099;



mt19937 rng(chrono::high_resolution_clock::now().time_since_epoch().count());
template<typename T>
static T randint(T lo, T hi) { return uniform_int_distribution<T>(lo, hi)(rng); }

int n;
vector<int>g[maxn];
int cur[maxn];
vector<int>blocks[1000];

int find_block(int x){
    return (x/sqr)+1;
}

int query(int a,int b){
    int res = 0;

    for(int i=a;i<=b;i++){
        if(find_block(i) != find_block(a))break;
        if(cur[i] > b)res++;
    }

    if(find_block(a) != find_block(b)){
        for(int i=b;i>=a;i--){
            if(find_block(i) != find_block(b))break;
            if(cur[i] > b)res++;
        }
    }

    for(int i=find_block(a)+1;i<find_block(b);i++){
        res += blocks[i].size()-(upper_bound(blocks[i].begin(),blocks[i].end(),b) - blocks[i].begin());
    }
    return res;
}


main(){
    ios_base::sync_with_stdio(0);
    cin.tie(0);

    int k;
    cin >> n >> k;

    for(int i=1;i<=n;i++){
        int x;cin >> x;
        g[x].pb(i);
        cur[i] = n + 1;
    }

    for(int i=1;i<=100000;i++){
        for(int j=0;j<g[i].size();j++){
            int in = g[i][j];
            int p = j + k;
            if(p < g[i].size()){
                cur[in] = g[i][p];
            }
        }
    }

    for(int i=1;i<=n;i++){
        blocks[find_block(i)].pb(cur[i]);
    }

    for(int i=1;i<1000;i++)
        sort(blocks[i].begin(),blocks[i].end());

    int last = 0;

    int q;cin >> q;
    for(int i=1;i<=q;i++){
        int l,r;
        cin >> l >> r;

        l = (last + l) % n;
        r = (last + r) % n;
        l++;
        r++;

        if(l > r)swap(l,r);
        last = query(l,r);
        cout << last << '\n';
    }









}
/*
10 2
1 2 3 4 5 6 7 8 9 10
2 2 8 7
3 1 10

*/


/**
55
17
*/
