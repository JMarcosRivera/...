#include<bits/stdc++.h>
#include<ext/pb_ds/assoc_container.hpp>
#include<ext/pb_ds/tree_policy.hpp>
#define db(x) cerr << #x << ": " << (x) << '\n'
#define maxn 1010000
#define pb push_back
#define f first
#define int long long
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
}
/// Prime Numbers:
/// 2, 173, 179, 181, 197, 311, 331, 737, 1009, 2011, 2027, 3079, 4001, 10037, 10079, 20011, 20089;
/// 100003, 100019, 100043, 200003, 200017, 1000003, 1000033, 1000037, 1000081;
/// 2000003, 2000029, 2000039, 1000000007, 1000000021, 2000000099;



mt19937 rng(chrono::high_resolution_clock::now().time_since_epoch().count());
template<typename T>
static T randint(T lo, T hi) { return uniform_int_distribution<T>(lo, hi)(rng); }

int p[maxn],ans[maxn],dp[maxn];
int sz[maxn];

struct SuffixArray {
    vector <int> sa, lcp, pos;
    SuffixArray(string &s, int lim = 256) {
        int n = s.size() + 1, k = 0, a, b;
        vector <int> x(all(s) + 1), y(n), ws(max(n, lim));
        sa = lcp = pos = y, iota(all(sa), 0);
        for(int j = 0, p = 0; p < n; j = max((int)1, j * 2), lim = p) {
            p = j, iota(all(y), n - j);
            for(int i = 0; i < n; i++)
                if(sa[i] >= j)
                    y[p++] = sa[i] - j;
            fill(all(ws), 0);
            for(int i = 0; i < n; i++)
                ws[x[i]]++;
            for(int i = 1; i < lim; i++) ws[i] += ws[i - 1];
            for(int i = n; i--;) sa[--ws[x[y[i]]]] = y[i];
            swap(x, y), p = 1, x[sa[0]] = 0;
            for(int i = 1; i < n; i++) {
                a = sa[i - 1], b = sa[i];
                x[b] = (y[a] == y[b] && y[a + j] == y[b + j]) ? p - 1 : p++;
            }
        }
        for(int i = 1; i < n; i++)
            pos[sa[i]] = i;
        for(int i = 0, j; i < n - 1; lcp[pos[i++]] = k)
            for(k && k--, j = sa[pos[i] - 1];
                    s[i + k] == s[j + k] && s[i+k] != '$'; k++);
    }
} ;

int rmq[maxn][22];
int n;

void build(SuffixArray &sa){
    for(int i=1;i<=n;i++){
        rmq[i][0] = sa.lcp[i+1];
    }
    for(int j=1;j<20;j++){
        for(int i=1;i<=n;i++){
            int p = i + (1ll << j) - 1;
            if(p <= n)
                rmq[i][j] = min(rmq[i][j-1],rmq[i+(1ll<<(j-1))][j-1]);
            else break;
        }
    }
}
int Min(int a,int b){
    int lg = log2(b-a+1);
    int ans = min(rmq[a][lg],rmq[b-(1ll<<lg)+1][lg]);
    return ans;
}

main(){
    ios_base::sync_with_stdio(0);
    cin.tie(0);

    string s;
    cin >> s;

    n = s.size();

    SuffixArray sa = SuffixArray(s);
    build(sa);

    for(int i=1;i<=n;i++){
        dp[i] = dp[i-1] + n - sa.sa[i];
    }

    int k;
    cin >> k;

    int sum = 0;
    int cur = 1;

    while(dp[cur] < k){
        cur++;
    }

  //  cout << cur << '\n';

    int lower = 0;
    int i=1;

    cur = max((int)1,cur-1);

    bool ok = 0;
    for(i=1;i<=n-sa.sa[cur];i++){

        int l = cur , r = n+1;
        int mid;

        while(l + 1 < r){
            mid = (l + r)/2;
            if(Min(cur,mid-1) >= i){
                l = mid;
            }
            else r = mid;
        }

        lower += (l-cur+1);

        r = cur;l = 0;

        while(l + 1 < r){
            mid = (l + r)/2;
            if(Min(mid,cur-1) >= i){
                r = mid;
            }
            else l = mid;
        }

        int s = dp[cur-1];
        int range = dp[cur-1] - dp[r-1];
        int szRange = cur-r;
        s = s - range + szRange*i;
        if(lower+s >= k){
            ok = 1;
            break;
        }
    }
    //cout << i << '\n';

    if(ok){
        string ans="";
        for(int j=sa.sa[cur];j<sa.sa[cur]+i;j++){
            ans+=s[j];
        }
        cout << ans << '\n';
    }
    else {
        cur++;
        lower = 0;
        i = 1;
        for(i=1;i<=n-sa.sa[cur];i++){

            int l = cur , r = n+1;
            int mid;

            while(l + 1 < r){
                mid = (l + r)/2;
                if(Min(cur,mid-1) >= i){
                    l = mid;
                }
                else r = mid;
            }

            lower += (l-cur+1);

            r = cur;l = 0;

            while(l + 1 < r){
                mid = (l + r)/2;
                if(Min(mid,cur-1) >= i){
                    r = mid;
                }
                else l = mid;
            }

            int s = dp[cur-1];
            int range = dp[cur-1] - dp[r-1];
            int szRange = cur-r;
            s = s - range + szRange*i;
            if(lower+s >= k){
                ok = 1;
                break;
            }


        }
                string ans="";
        for(int j=sa.sa[cur];j<sa.sa[cur]+i;j++){
            ans+=s[j];
        }
        cout << ans << '\n';


    }





}
