#include<bits/stdc++.h>
using namespace std;
 
#define db(x) cerr << #x << ": " << x << '\n';
 
#define maxn 100010
 
int depth[maxn],sz[maxn];
vector<int>g[maxn];
int st[maxn*4],lazy[maxn*4];
 
void dfs(int u,int p=0){
    if(g[u].size() >= 2 && g[u][0] == p)swap(g[u][0],g[u].back());
    sz[u]=1;
    depth[u]=depth[p]+1;
    for(int j=0;j<g[u].size();j++){
        int i=g[u][j];
        if(i != p){
            dfs(i , u);
            sz[u]+=sz[i];
            if(sz[i] > sz[g[u][0]])swap(g[u][0],g[u][j]);
        }
    }
}
int parent[maxn],head[maxn],tin[maxn],t=0,n;
 
void propagate(int nod,int l,int r){
    if(lazy[nod] == -1)return;
    st[nod] = (lazy[nod] * (r-l+1));
    if(l != r){
        lazy[nod*2] = lazy[nod];
        lazy[nod*2 + 1] = lazy[nod];
    }
    lazy[nod] = -1;
}
 
void update(int a,int b,int x,int nod=1,int l=1,int r=n){
    propagate(nod,l,r);
    if(b < l or a > r)return;
    if(l >= a && r <= b){
        lazy[nod] = x;
        propagate(nod,l,r);
        return;
    }
    int mid=(l+r)/2;
    int ls=2*nod,rs=ls+1;
    update(a,b,x,ls,l,mid);
    update(a,b,x,rs,mid+1,r);
    st[nod] = st[ls] + st[rs];
}
int query(int a,int b,int nod=1,int l=1,int r=n){
    propagate(nod,l,r);
    if(b < l or a > r)return 0;
    if(l >= a && r <= b)return st[nod];
    int ls = 2*nod , rs = ls + 1 , mid = (l + r)/2;
    return query(a,b,ls,l,mid) + query(a,b,rs,mid+1,r);
}
 
void euler_tour(int u,int p=0,int __head=1){
    tin[u]=++t;
    head[u]=__head;
    parent[u]=p;
    for(int i=0;i<g[u].size();i++){
        int v=g[u][i];
        if(v != p){
            euler_tour(v,u,(i==0) ? __head : v);
        }
    }
}
 
void update_path(int a , int b,int x){
    while(head[a] != head[b]){
        if(depth[head[a]] < depth[head[b]])swap(a,b);
       // db(head[a]);
       // db(a);
        update(tin[head[a]],tin[a],x);
        a = parent[head[a]];
    }
    if(depth[a] < depth[b])swap(a,b);
   // db(b);
   // db(a);
    update(tin[b],tin[a],x);
}
int intersection(int a,int b){
    int ans = 0;
    while(head[a] != head[b]){
        if(depth[head[a]] < depth[head[b]] )swap(a,b);
        ans += query(tin[head[a]],tin[a]);
        a = parent[head[a]];
    }
    if(depth[a] < depth[b])swap(a,b);
    ans += query(tin[b],tin[a]);
    return ans;
}
 
 
main(){
    ios_base::sync_with_stdio(0);
    cin.tie(0);
 
    int q;
    cin >> n >> q;
 
    for(int i=1;i<n;i++){
        int a,b;
        cin >> a >> b;
        g[a].push_back(b);
        g[b].push_back(a);
    }
 
    dfs(1);
    euler_tour(1);
 
    memset(lazy,-1,sizeof(lazy));
    while(q--){
        int a,b,c,d;
        cin >> a >> b >> c >> d;
 
        update_path(a,b,1);
 
        cout << intersection(c,d) << '\n';
        update_path(a,b,0);
    }
 
}
