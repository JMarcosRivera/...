#include<bits/stdc++.h>
#include<ext/pb_ds/assoc_container.hpp>
#include<ext/pb_ds/tree_policy.hpp>
#define db(x) cerr << #x << ": " << (x) << '\n'
#define maxn 210000
#define pb push_back
#define f first
#define s second
#define X real()
#define Y imag()
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


bool is_vowel(char c){
    if(c == 'a' or c == 'e' or c == 'i' or c == 'u' or c == 'o' or c == 'y'){
        return 1;
    }
    return 0;
}
double x[3],y[3];
bool ok(int i,int j){
    if(y[i] == y[j] or x[i] == x[j]){
        return 0;
    }
    return 1;
}
int sum(int s){
    int ans = 0;
    while(s){
        ans += (s % 10);
        s /= 10;
    }
    return ans;
}

mt19937 rnd(chrono::steady_clock::now().time_since_epoch().count());

struct treap {
  //This is an implicit treap which investigates here on an array
  struct node {
    int val, sz, prior, lazy, sum, mx, mn, repl;
    bool repl_flag, rev;
    node *l, *r, *par;
    node() {
      lazy = 0;
      rev = 0;
      sum = 0;
      val = 0;
      sz = 0;
      mx = 0;
      mn = 0;
      repl = 0;
      repl_flag = 0;
      prior = 0;
      l = NULL;
      r = NULL;
      par = NULL;
    }
    node(int _val) {
      val = _val;
      sum = _val;
      mx = _val;
      mn = _val;
      repl = 0;
      repl_flag = 0;
      rev = 0;
      lazy = 0;
      sz = 1;
      prior = rnd();
      l = NULL;
      r = NULL;
      par = NULL;
    }
  };
  typedef node* pnode;
  pnode root;
  pnode position[maxn];//positions of all the values
  //clearing the treap
  void clear() {
    root = NULL;
    for(int i=0;i<maxn;i++)position[i] = pnode();
  }

  treap() {
    clear();
  }

  int size(pnode t) {
    return t ? t->sz : 0;
  }
  void update_size(pnode &t) {
    if(t) t->sz = size(t->l) + size(t->r) + 1;
  }

  void update_parent(pnode &t) {
    if(!t) return;
    if(t->l) t->l->par = t;
    if(t->r) t->r->par = t;
  }
  //add operation
  void lazy_sum_upd(pnode &t) {
    if( !t or !t->lazy )    return;
    t->sum += t->lazy * size(t);
    t->val += t->lazy;
    t->mx += t->lazy;
    t->mn += t->lazy;
    if( t->l )  t->l->lazy += t->lazy;
    if( t->r )  t->r->lazy += t->lazy;
    t->lazy = 0;
  }
  //replace update
  void lazy_repl_upd(pnode &t) {
    if( !t or !t->repl_flag )   return;
    t->val = t->mx = t->mn = t->repl;
    t->sum = t->val * size(t);
    if( t->l ) {
      t->l->repl = t->repl;
      t->l->repl_flag = true;
    }
    if( t->r ) {
      t->r->repl = t->repl;
      t->r->repl_flag = true;
    }
    t->repl_flag = false;
    t->repl = 0;
  }
  //reverse update
  void lazy_rev_upd(pnode &t) {
    if( !t or !t->rev ) return;
    t->rev = false;
    swap(t->l, t->r);
    if( t->l )  t->l->rev ^= true;
    if( t->r )  t->r->rev ^= true;
  }
  //reset the value of current node assuming it now
  //represents a single element of the array
  void reset(pnode &t) {
    if(!t) return;
    t->sum = t->val;
    t->mx = t->val;
    t->mn = t->val;
  }
  //combine node l and r to form t by updating corresponding queries
  void combine(pnode &t, pnode l, pnode r) {
    if(!l) {
      t = r;
      return;
    }
    if(!r) {
      t = l;
      return;
    }
    //Beware!!!Here t can be equal to l or r anytime
    //i.e. t and (l or r) is representing same node
    //so operation is needed to be done carefully
    //e.g. if t and r are same then after t->sum=l->sum+r->sum operation,
    //r->sum will be the same as t->sum
    //so BE CAREFUL
    t->sum = l->sum + r->sum;
    t->mx = max(l->mx, r->mx);
    t->mn = min(l->mn, r->mn);
  }
  //perform all operations
  void operation(pnode &t) {
    if( !t )    return;
    reset(t);
    lazy_rev_upd(t->l);
    lazy_rev_upd(t->r);
    lazy_repl_upd(t->l);
    lazy_repl_upd(t->r);
    lazy_sum_upd(t->l);
    lazy_sum_upd(t->r);
    combine(t, t->l, t);
    combine(t, t, t->r);
  }
  //split node t in l and r by key k
  //so first k+1 elements(0,1,2,...k) of the array from node t
  //will be split in left node and rest will be in right node
  void split(pnode t, pnode &l, pnode &r, int k, int add = 0) {
    if(t == NULL) {
      l = NULL;
      r = NULL;
      return;
    }
    lazy_rev_upd(t);
    lazy_repl_upd(t);
    lazy_sum_upd(t);
    int idx = add + size(t->l);
    if(idx <= k)
      split(t->r, t->r, r, k, idx + 1), l = t;
    else
      split(t->l, l, t->l, k, add), r = t;

    update_parent(t);
    update_size(t);
    operation(t);
  }
  //merge node l with r in t
  void merge(pnode &t, pnode l, pnode r) {
    lazy_rev_upd(l);
    lazy_rev_upd(r);
    lazy_repl_upd(l);
    lazy_repl_upd(r);
    lazy_sum_upd(l);
    lazy_sum_upd(r);
    if(!l) {
      t = r;
      return;
    }
    if(!r) {
      t = l;
      return;
    }

    if(l->prior > r->prior)
      merge(l->r, l->r, r), t = l;
    else
      merge(r->l, l, r->l), t = r;

    update_parent(t);
    update_size(t);
    operation(t);
  }
  //insert val in position a[pos]
  //so all previous values from pos to last will be right shifted
  void insert(int pos, int val) {
    if(root == NULL) {
      pnode to_add = new node(val);
      root = to_add;
      position[val] = root;
      return;
    }

    pnode l, r, mid;
    mid = new node(val);
    position[val] = mid;

    split(root, l, r, pos - 1);
    merge(l, l, mid);
    merge(root, l, r);
  }
  //erase from qL to qR indexes
  //so all previous indexes from qR+1 to last will be left shifted qR-qL+1 times
  void erase(int qL, int qR) {
    pnode l, r, mid;

    split(root, l, r, qL - 1);
    split(r, mid, r, qR - qL);
    merge(root, l, r);
  }
  //returns answer for corresponding types of query
  int query(int qL, int qR) {
    pnode l, r, mid;

    split(root, l, r, qL - 1);
    split(r, mid, r, qR - qL);

    int answer = mid->sum;
    merge(r, mid, r);
    merge(root, l, r);

    return answer;
  }
  //add val in all the values from a[qL] to a[qR] positions
  void update(int qL, int qR, int val) {
    pnode l, r, mid;

    split(root, l, r, qL - 1);
    split(r, mid, r, qR - qL);
    lazy_repl_upd(mid);
    mid->lazy += val;

    merge(r, mid, r);
    merge(root, l, r);
  }
  //reverse all the values from qL to qR
  void reverse(int qL, int qR) {
    pnode l, r, mid;

    split(root, l, r, qL - 1);
    split(r, mid, r, qR - qL);

    mid->rev ^= 1;
    merge(r, mid, r);
    merge(root, l, r);
  }
  //replace all the values from a[qL] to a[qR] by v
  void replace(int qL, int qR, int v) {
    pnode l, r, mid;

    split(root, l, r, qL - 1);
    split(r, mid, r, qR - qL);
    lazy_sum_upd(mid);
    mid->repl_flag = 1;
    mid->repl = v;
    merge(r, mid, r);
    merge(root, l, r);
  }
  //it will cyclic right shift the array k times
  //so for k=1, a[qL]=a[qR] and all positions from ql+1 to qR will
  //have values from previous a[qL] to a[qR-1]
  //if you make left_shift=1 then it will to the opposite
  void cyclic_shift(int qL, int qR, int k, bool left_shift = 0) {
    if(qL == qR) return;
    k %= (qR - qL + 1);

    pnode l, r, mid, fh, sh;
    split(root, l, r, qL - 1);
    split(r, mid, r, qR - qL);

    if(left_shift == 0) split(mid, fh, sh, (qR - qL + 1) - k - 1);
    else split(mid, fh, sh, k - 1);
    merge(mid, sh, fh);

    merge(r, mid, r);
    merge(root, l, r);
  }
  bool exist;
  //returns index of node curr
  int get_pos(pnode curr, pnode son = nullptr) {
    if(exist == 0) return 0;
    if(curr == NULL) {
      exist = 0;
      return 0;
    }
    if(!son) {
      if(curr == root) return size(curr->l);
      else return size(curr->l) + get_pos(curr->par, curr);
    }

    if(curr == root) {
      if(son == curr->l) return 0;
      else return size(curr->l) + 1;
    }

    if(curr->l == son) return get_pos(curr->par, curr);
    else return get_pos(curr->par, curr) + size(curr->l) + 1;
  }
  //returns index of the value
  //if the value has multiple positions then it will
  //return the last index where it was added last time
  //returns -1 if it doesn't exist in the array
  int get_pos(int value) {
    if(position[value] == NULL) return -1;
    exist = 1;
    int x = get_pos(position[value]);
    if(exist == 0) return -1;
    else return x;
  }
  //returns value of index pos
  int get_val(int pos) {
    return query(pos, pos);
  }
  //returns size of the treap
  int size() {
    return size(root);
  }
  //inorder traversal to get indexes chronologically
  void inorder(pnode cur) {
    if(cur == NULL) return;
    operation(cur);
    inorder(cur->l);
    cout << cur->val << ' ';
    inorder(cur->r);
  }
  //print current array values serially
  void print_array() {
//      for(int i=0;i<size();i++) cout<<get_val(i)<<' ';
//      cout<<nl;
    inorder(root);

  }
  bool find(int val) {
    if(get_pos(val) == -1) return 0;
    else return 1;
  }
};

treap t;

int a[maxn];
main(){
    ios_base::sync_with_stdio(0);
    cin.tie(0);

    int n,m,q;
    cin >> n  >> q;

    string s;
    cin >> s;
    for(int i=0;i<n;i++){
        t.insert(i,(int)s[i]);
    }

    while(q--){
        int a,b;
        cin >> a >> b;
        a--;
        b--;

        int sz = (b-a+1);
        int sz1 = (n-a) - sz;

        t.reverse(a,n-1);
        t.reverse(n-sz,n-1);

        if(sz1>0)t.reverse(a,a+sz1-1);
    }

    for(int i=0;i<n;i++){
        cout << (char)(t.query(i,i)) ;
    }



}
