#include<bits/stdc++.h>
#include<malloc.h>
#include "Regex2MinDFA.h"
#include<unordered_map>
using namespace std;
#define settype int
typedef pair<double, int> DI;
typedef pair<int, int> II;
typedef unordered_map<settype, double> USD;
typedef pair<settype, double> SD;
typedef pair<int, vector<SD>> IV;
const int MAX_V = 1070378;
int N, M;//# of vertices and edges
long long hopsize, npathConcat;//# of path concatenations
double optw = DBL_MAX;//optimal answer
int treeheight = 0, treewidth = 0, treeavgheight = 0;
#define PI 3.14
#define RADIO_TERRESTRE 6370000.0
#define GRADOS_RADIANES PI / 180
typedef pair<double, double> DD;
vector<DD> coords;

double calculateDistance(int u, int v) {
    double latitud1 = coords[u].second, longitud1 = coords[u].first, latitud2 = coords[v].second, longitud2 = coords[v].first;
    double haversine;
    double temp;
    double distancia_puntos;

    latitud1  = latitud1  * GRADOS_RADIANES;
    longitud1 = longitud1 * GRADOS_RADIANES;
    latitud2  = latitud2  * GRADOS_RADIANES;
    longitud2 = longitud2 * GRADOS_RADIANES;

    haversine = (pow(sin((1.0 / 2) * (latitud2 - latitud1)), 2)) + ((cos(latitud1)) * (cos(latitud2)) * (pow(sin((1.0 / 2) * (longitud2 - longitud1)), 2)));
    temp = 2 * asin(min(1.0, sqrt(haversine)));
    distancia_puntos = RADIO_TERRESTRE * temp;

   return distancia_puntos-0.3;
}
typedef struct node{
    int depth;
    int ran;//rank in the order
    int parent;
    vector<int> children;
    vector<int> X;
};
node T[MAX_V];

struct edge{
    int from, to;
    double weight;
    char label;
    int id;
    double tldis1, tldis2, tldis12;
    edge(int a,int b,double w,char l){
        from = a, to = b, weight = w, label = l;
    }
    bool operator <(const edge p) const{
        return id < p.id;
    }
};
vector<vector<double>> Lu[MAX_V];//for distances
vector<double> Lh2h[MAX_V];
int maplabel[26];
vector<IV> L[MAX_V];//supersets
vector<int> anc[MAX_V];
int root = -1;
unordered_map<int, USD> adj[MAX_V];//contains only edges to higher rank
//unordered_map<int, double> adju[MAX_V];//contains only edges to higher rank
unordered_map<int,int> adjo[MAX_V], adjT[MAX_V];//contains all the edges
vector<edge> adjL[MAX_V];
int allowedLabel[MAX_LS];
settype allowedLabels;
int nsym;
int logn2[1 << 27];
int nlm; //number of landmarks
vector<int> lminds;
vector<vector<double>> lm;
int mapallowlabel[1 << 22];
vector<int> rmapallowlabel;

vector<int> order;
bool flag[MAX_V];
bool cmp(const int &a, const int &b){
    return T[a].ran > T[b].ran;
}

vector<int> ordergen;
int del[MAX_V];//deleted neighbors
double update(int v){
//priorities for contracting vertices
    return 1000 * adjo[v].size() + del[v];
}
typedef pair<II, int> III;
void genorder(string filename, bool writeflag){
//first generating an order of contracting vertices
    priority_queue<II, vector<II>, greater<II> > degque;
    for (int i = 0; i < N; i++)
        degque.push(II(update(i), i));
    int iter = -1, totnewedge = 0;
    while(!degque.empty()){
        II ii = degque.top();
        degque.pop();
        int v = ii.second;
        if(flag[v])
            continue;
        double pri = update(v);
        if (pri > degque.top().first){//lazy update
            degque.push(II(pri,v));
            continue;
        }
        iter += 1;
        flag[v] = 1;
        ordergen.push_back(v);
        T[v].ran = iter;
        unordered_map<int, int>::iterator it;
        vector<int> nei;
        for (it = adjo[v].begin(); it !=adjo[v].end(); it++)
            if(!flag[it->first])
                nei.push_back(it->first);
        int lenX = nei.size();
        for (int j = 0; j < lenX; j++){
            int u = nei[j];
            for (int k = j + 1; k < lenX; k++){
                int w = nei[k];
                if(adjo[u].count(w)==0){
                    adjo[u][w] = 1;
                    adjo[w][u] = 1;
                    totnewedge += 1;
                }
            }
            //adjo[u].erase(v);
            del[u]++;
        }
    }
    if(writeflag){
        FILE *fp_order = fopen(filename.c_str(), "w");
        for (int i = 0; i < N;i++){
            fprintf(fp_order, "%d\n", T[i].ran);
        }
        fclose(fp_order);
    }
}

void LSDSJoin(USD &P1, USD &P2, USD &res){
    //return the res contains the paths of joining P1 and P2
    USD::iterator it1, it2;
    for (it1 = P1.begin(); it1 != P1.end(); it1++){
        settype set1 = it1->first;
        for (it2 = P2.begin(); it2 != P2.end(); it2++){
            settype set2 = it2->first;
            double dis = it1->second + it2->second;
            settype uni = set1 | set2;
            if(res.count(uni)){
                if(dis < res[uni])
                    res[uni] = dis;
            }
            else{
                res[uni] = dis;
            }
        }           
    }
}

void LSDSPrune(USD &res){
    vector<settype> era;
    USD::iterator it, jt;
    for (it = res.begin(); it != res.end();it++){
        for (jt = res.begin(); jt != res.end();jt++){
            settype s1 = it->first, s2 = jt->first;
            if (s2 == s1)
                continue;
            double dis1 = it->second, dis2 = jt->second;
            if (((s1 & s2) == s1) && (dis1 <= dis2)){
                era.push_back(s2);
            }
        }
    }
    for (int i = 0; i < era.size();i++)
        res.erase(era[i]);
}

double maxlabelsize, avglabelsize;
int descnt[MAX_V];
vector<int> ancarray[MAX_V];//the indices (or depth) for X(v)'s nodes
queue<int> bfs, bfssave, bfsanc;
void treedec(){
    for (int i = 0; i < N; i++){
        int v = ordergen[i];
        if(i%100000==0)
            printf("%d\n", i);
        unordered_map<int, int>::iterator it;  
        for (it = adjT[v].begin(); it !=adjT[v].end(); it++)
            T[v].X.push_back(it->first);
        int lenX = T[v].X.size();
        for (int j = 0; j < lenX; j++){
            int u = T[v].X[j];
            //printf("u%d:", u+1);
            for (int k = j + 1; k < lenX; k++){
                int w = T[v].X[k];
                //printf("w%d ", w + 1);
                if(T[u].ran<T[w].ran){
                    if(adjT[u].count(w)==0){
                        adjT[u][w] = 1;
                    }
                    LSDSJoin(adj[v][u], adj[v][w], adj[u][w]);
                    LSDSPrune(adj[u][w]);         
                    //printUSD(adj[u][w]);
                }
                else{
                    if(adjT[w].count(u)==0){
                        adjT[w][u] = 1;
                    }
                    LSDSJoin(adj[v][u], adj[v][w], adj[w][u]);
                    LSDSPrune(adj[w][u]);
                    //printUSD(adj[w][u]);
                }
            }
        }
    }
    //from bottom to top
    for (int i = 0; i < ordergen.size();i++){
        int v = ordergen[i];
        sort(T[v].X.begin(), T[v].X.end(), cmp);
        int lenx = T[v].X.size();
        if (lenx != 0)
            T[v].parent = T[v].X[lenx - 1];
        else
            T[v].parent = MAX_V;
        T[v].X.push_back(v);
        treewidth = max(treewidth, lenx + 1);
        if (T[v].parent == MAX_V){
            root = v;
            break;
        }
        T[T[v].parent].children.push_back(v);
    }
}
bool cmpSD(const SD &a, const SD &b){
    return a.second < b.second;
}
long long indexsize, totalwidth;
int set11, set21;
void generateLabel4v(int v){
    //generate labels for each X(v) and its ancestors 
    vector<int> anc;
    int u1 = v;
    while (T[u1].parent != MAX_V){
        anc.push_back(T[u1].parent);
        u1 = T[u1].parent;
    }
    int lenanc = anc.size();
    T[v].depth = lenanc;
    treeavgheight += (double)lenanc;
    treeheight = max(treeheight, lenanc + 1);
    for (int i = 0; i < lenanc;i++){
        int u = anc[anc.size() - 1 - i];
        int lenx = T[v].X.size();
        for (int k = 0; k < lenx; k++){
            int w = T[v].X[k];
            if (w == v || w == u){
                if (w == u)
                    ancarray[v].push_back(i);
                continue;
            }
            if(T[u].ran<T[w].ran){
                LSDSJoin(adj[v][w], adj[u][w], adj[v][u]);
                LSDSPrune(adj[v][u]);
            }
            else{
                LSDSJoin(adj[v][w], adj[w][u], adj[v][u]);
                LSDSPrune(adj[v][u]);
            }
        }
        USD::iterator it;
        vector<SD> tmp;
        vector<double> tmpm(22, DBL_MAX);
        double h2hdis = DBL_MAX;
        for (it = adj[v][u].begin(); it != adj[v][u].end();it++){
            int s1 = it->first;
            double dis = it->second;
            tmp.push_back(SD(s1, dis));
            int intc = logn2[s1];
            if ((intc != -1) && maplabel[intc]){
                tmpm[maplabel[intc] - 1] = dis;
            }
            for (int k = 0; k < 10;k++){
                int seti1 = rmapallowlabel[k];
                if ((s1 & seti1) == s1)
                    tmpm[mapallowlabel[seti1]] = min(tmpm[mapallowlabel[seti1]], dis);
            }
            h2hdis = min(dis, h2hdis);
        }
        sort(tmp.begin(), tmp.end(), cmpSD);
        L[v].push_back(make_pair(u, tmp));
        Lu[v].push_back(tmpm);
        Lh2h[v].push_back(h2hdis);
        maxlabelsize = max(maxlabelsize, (double)tmp.size());
        avglabelsize += (double)tmp.size();
        //printf("%d %d:\n", v+1,u+1);
        //printSD(tmp);
    }
    vector<SD> tmp;
    L[v].push_back(make_pair(v, tmp));
    vector<double> tmpz(22, 0);
    Lu[v].push_back(tmpz);
    Lh2h[v].push_back(0);
    ancarray[v].push_back(lenanc);
    totalwidth += T[v].X.size();
}
void labeling(){
    //label in a top-down manner
    for (int i = 0; i < 10;i++)
        set11 = set11 | (1 << i);
    for (int i = 10; i < 20;i++)
        set21 = set21 | (1 << i);

    memset(mapallowlabel, -1, sizeof(mapallowlabel));
    int set1 = 0, set2 = 0;
    int a = 0, b = 5, c = 10, d = 15;
    int mn = 10;
    for (int i = 0; i < 5;i++){
        set1 = set1 | (1 << (d + i)) | (1 << (c + i));
        rmapallowlabel.push_back(set1);
        mapallowlabel[set1] = mn++;
        set2 = set2 | (1 << (a + i)) | (1 << (b + i));
        mapallowlabel[set2] = mn++;
        rmapallowlabel.push_back(set2);
    }
    bfs.push(root);
    int iter = 0;
    while(!bfs.empty()){
        int v= bfs.front();
        bfs.pop();
        generateLabel4v(v);
        for (int i = 0; i < T[v].children.size();i++){
            bfs.push(T[v].children[i]);
        }
        if(iter%100000==0)
            printf("%d %d\n", iter, treeheight);
        iter += 1;
    }
}


vector < int > adjt[MAX_V];    // stores the tree
vector < int > euler;      // tracks the eulerwalk
vector < int > depthArr;   // depth for each node corresponding
                           // to eulerwalk
 
int FAI[2*MAX_V];     // stores first appearance index of every node
int level[2*MAX_V];   // stores depth for all nodes in the tree
int ptr;         // pointer to euler walk
int dp[2*MAX_V][30];  // sparse table
int logn[2*MAX_V];    // stores log values
int p2[30];      // stores power of 2
 
void buildSparseTable(int n)
{
    // initializing sparse table
    memset(dp,-1,sizeof(dp));
 
    // filling base case values
    for (int i=1; i<n; i++)
        dp[i-1][0] = (depthArr[i]>depthArr[i-1])?i-1:i;
 
    // dp to fill sparse table
    for (int l=1; l<28; l++)
      for (int i=0; i<n; i++)
        if (dp[i][l-1]!=-1 && dp[i+p2[l-1]][l-1]!=-1)
          dp[i][l] =
            (depthArr[dp[i][l-1]]>depthArr[dp[i+p2[l-1]][l-1]])?
             dp[i+p2[l-1]][l-1] : dp[i][l-1];
        else
             break;
}
 
int query(int l,int r)
{
    int d = r-l;
    int dx = logn[d];
    if (l==r) return l;
    if (depthArr[dp[l][dx]] > depthArr[dp[r-p2[dx]][dx]])
        return dp[r-p2[dx]][dx];
    else
        return dp[l][dx];
}
 
void preprocess()
{
    // memorizing powers of 2
    p2[0] = 1;
    for (int i=1; i<28; i++)
        p2[i] = p2[i-1]*2;
 
    // memorizing all log(n) values
    int val = 1,ptr=0;
    for (int i=1; i<2*MAX_V; i++)
    {
        logn[i] = ptr-1;
        if (val==i)
        {
            val*=2;
            logn[i] = ptr;
            ptr++;
        }
    }
}

void dfs(int cur,int prev,int dep)
{
    // marking FAI for cur node
    if (FAI[cur]==-1)
        FAI[cur] = ptr;
 
    level[cur] = dep;
 
    // pushing root to euler walk
    euler.push_back(cur);
 
    // incrementing euler walk pointer
    ptr++;
 
    for (auto x:adjt[cur])
    {
        if (x != prev)
        {
            dfs(x,cur,dep+1);
 
            // pushing cur again in backtrack
            // of euler walk
            euler.push_back(cur);
 
            // increment euler walk pointer
            ptr++;
        }
    }
}
 
// Create Level depthArray corresponding
// to the Euler walk Array
void makeArr()
{
    for (auto x : euler)
        depthArr.push_back(level[x]);
}
 
int LCA(int u,int v)
{
    // trivial case
    if (u==v)
       return u;
 
    if (FAI[u] > FAI[v])
       swap(u,v);
 
    // doing RMQ in the required range
    return euler[query(FAI[u], FAI[v])];
}
void lcamain()
{
    // constructing the described tree
    for (int i = 1; i <= N; i++){
        int u = i, v = T[i - 1].parent + 1;
        if (u == root + 1)
            continue;
        adjt[u].push_back(v);
        adjt[v].push_back(u);
    }
    
    // performing required precalculations
    preprocess();
    // doing the Euler walk
    ptr = 0;
    memset(FAI,-1,sizeof(FAI));
    dfs(root+1, 0, 0);

    // creating depthArray corresponding to euler[]
    makeArr();
 
    // building sparse table
    buildSparseTable(depthArr.size());
}

typedef pair<int, settype> IS;
typedef struct cp{
    int sv, lv;
    settype tlabel;
    cp(int _sv, int _lv, settype _tlab){
        sv = _sv, lv = _lv, tlabel = _tlab;
    }
    bool operator <(const cp p) const{
        return sv < p.sv;
    }
};
typedef pair<int, cp> CP;
unordered_map<int, vector<settype>> Lc[MAX_V];
vector<edge> G[MAX_V];
bool ccquery(int s,int t, settype l){
    unordered_map<int, vector<settype>>::iterator it;
    for (it = Lc[s].begin(); it != Lc[s].end();it++){
        int v = it->first;
        for (int i = 0; i < it->second.size();i++){
            settype s = it->second[i];
            if((s&l)==s &&Lc[t].count(v)){
                for (int j = 0; j < Lc[t][v].size();j++){
                    if((Lc[t][v][j]&l)==Lc[t][v][j])
                        return true;
                }
            }
        }
    }
    return false;
}

void P2H(){
    for (int i = 0; i < N; i++){
        int v = ordergen[i];
        //printf("%d:\n", v);
        priority_queue<CP, vector<CP>, greater<CP>> pque;
        Lc[v][v].push_back(0);
        for (int j = 0; j < adjL[v].size();j++){
            pque.push(CP(1, cp(v, adjL[v][j].to, 1<<(adjL[v][j].label-'a'))));
        }
        while(pque.size()){
            CP c = pque.top();
            pque.pop();
            int len = c.first, slastv = c.second.sv, lastv = c.second.lv;
            settype s = c.second.tlabel;
            //printf("len%d v%d slastv%d lastv%d ", len, v, slastv, lastv);
            //printset(s);
            if(ccquery(v,lastv,s)){
                //printf("flagtrue\n");
                continue;
            }
            //printf("flagfalse\n");
            Lc[lastv][v].push_back(s);
            //Lc[v][lastv].push_back(s);
            for (int j = 0; j < adjL[lastv].size();j++){
                edge e = adjL[lastv][j];
                if(e.to==slastv)
                    continue;
                int cl = e.label - 'a';
                pque.push(CP(len + 1, cp(lastv, e.to, s | (1 << cl))));
            }
        }
    }
    /*printf("=======\n");
    printLc();
    printf("=======--------\n");*/
}

double h2hQuery(int s, int t, bool flag){
    optw = DBL_MAX;
    if (s == t)
        return 0;
    int l = LCA(s + 1, t + 1) - 1;
    //printf("-%d %d: %d\n", s + 1, t + 1, l + 1);
    int ind;
    if (l == s){//X(s) is an ancestor of X(t)
        return Lh2h[t][T[s].depth];
    }
    else if (l == t){//X(t) is an ancestor of X(s)
        return Lh2h[s][T[t].depth];
    }
    else{//find the LCA and cs and ct
        int cs, ct;
        for (int i = 0; i < T[l].children.size();i++){
            int tmp = T[l].children[i] + 1;
            if(LCA(s+1,tmp)==tmp)
                cs = tmp-1;
            if(LCA(t+1,tmp)==tmp)
                ct = tmp-1;
        }
        l = (ancarray[cs].size() < ancarray[ct].size()) ? cs : ct;
        if(ancarray[cs].size()==ancarray[ct].size())
            l = (cs < ct) ? cs : ct;
        //printf("*%d %d %d %d*\n", l + 1, cs+1, ct+1, ancarray[l].size());
        for (int i = 0; i + 1 < ancarray[l].size(); i++)//iterate over each hoplink
        {
            ind = ancarray[l][i];
            optw = min(optw, Lh2h[s][ind] + Lh2h[t][ind]);
        }
    }
    return optw;
}

double dist(int u, int ind, settype s){
    for (int i = 0; i < L[u][ind].second.size(); i++){
        settype s1 = L[u][ind].second[i].first;
        if ((s1 & s) == s1)
            return L[u][ind].second[i].second;
    }
    return DBL_MAX;
}
double LSDQuery(int s, int t, int allowedLabels){
    optw = DBL_MAX;
    if (s == t)
        return 0;
    if (s > t)
        swap(s, t);
    int l = LCA(s + 1, t + 1) - 1, ind;
    if(mapallowlabel[allowedLabels]!=-1){
        int lind = mapallowlabel[allowedLabels];
        if (l == s){//X(s) is an ancestor of X(t)
            return Lu[t][T[s].depth][lind];
        }
        else if (l == t){//X(t) is an ancestor of X(s)
            return Lu[s][T[t].depth][lind];
        }
        else{//find the LCA and cs and ct
            int cs, ct;
            for (int i = 0; i < T[l].children.size();i++){
                int tmp = T[l].children[i] + 1;
                if(LCA(s+1,tmp)==tmp)
                    cs = tmp-1;
                if(LCA(t+1,tmp)==tmp)
                    ct = tmp-1;
            }
            l = (ancarray[cs].size() < ancarray[ct].size()) ? cs : ct;
            if(ancarray[cs].size()==ancarray[ct].size())
                l = (cs < ct) ? cs : ct;
            //printf("*%d %d %d %d*\n", l + 1, cs+1, ct+1, ancarray[l].size());
            for (int i = 0; i + 1 < ancarray[l].size(); i++)//iterate over each hoplink
            {
                ind = ancarray[l][i];
                optw = min(optw, Lu[s][ind][lind] + Lu[t][ind][lind]);
            }
        }
        return optw;
    }
    int intlogall = logn2[allowedLabels];
    if((intlogall!=-1)&&maplabel[intlogall]){
        int lind = maplabel[intlogall] - 1;
        if (l == s){//X(s) is an ancestor of X(t)
            return Lu[t][T[s].depth][lind];
        }
        else if (l == t){//X(t) is an ancestor of X(s)
            return Lu[s][T[t].depth][lind];
        }
        else{//find the LCA and cs and ct
            int cs, ct;
            for (int i = 0; i < T[l].children.size();i++){
                int tmp = T[l].children[i] + 1;
                if(LCA(s+1,tmp)==tmp)
                    cs = tmp-1;
                if(LCA(t+1,tmp)==tmp)
                    ct = tmp-1;
            }
            l = (ancarray[cs].size() < ancarray[ct].size()) ? cs : ct;
            if(ancarray[cs].size()==ancarray[ct].size())
                l = (cs < ct) ? cs : ct;
            //printf("*%d %d %d %d*\n", l + 1, cs+1, ct+1, ancarray[l].size());
            for (int i = 0; i + 1 < ancarray[l].size(); i++)//iterate over each hoplink
            {
                ind = ancarray[l][i];
                optw = min(optw, Lu[s][ind][lind] + Lu[t][ind][lind]);
            }
        }
        return optw;
    }
    //printf("-%d %d: %d\n", s + 1, t + 1, l + 1);
    if (l == s){//X(s) is an ancestor of X(t)
        optw = dist(t, T[s].depth, allowedLabels);
    }
    else if (l == t){//X(t) is an ancestor of X(s)
        optw = dist(s, T[t].depth, allowedLabels);
    }
    else{//find the LCA and cs and ct
        int cs, ct;
        for (int i = 0; i < T[l].children.size();i++){
            int tmp = T[l].children[i] + 1;
            if(LCA(s+1,tmp)==tmp)
                cs = tmp-1;
            if(LCA(t+1,tmp)==tmp)
                ct = tmp-1;
        }
        l = (ancarray[cs].size() < ancarray[ct].size()) ? cs : ct;
        if(ancarray[cs].size()==ancarray[ct].size())
            l = (cs < ct) ? cs : ct;
        //printf("*%d %d %d*\n", l + 1, cs+1, ct+1);
        for (int i = 0; i + 1 < ancarray[l].size(); i++)//iterate over each hoplink
        {
            ind = ancarray[l][i];
            optw = min(optw, dist(s, ind, allowedLabels) + dist(t, ind, allowedLabels));
        }
    }
    //printf("%f\n", optw);
    return optw;
}

void setLabels(string regL){
    allowedLabels = 0;
    nsym = 0;
    for (int i = 0; i < MAX_LS;i++)
        allowedLabel[i] = 0;
    for (int i = 0; i < regL.size() - 1; i++){
        if (regL[i] == '(' || regL[i] == ' ')
            continue;
        int cat2 = regL[i + 1] - '0';
        cat2 = (cat2 > 5) ? 5 : cat2;
        char cat1 = regL[i];
        char l = (cat1 - 'A') * 5 + cat2 - 1 + 'a';
        if (allowedLabel[l - 'a'] == 0){
            allowedLabels = allowedLabels | (1 << (l - 'a'));
            nsym += 1;
        }
        allowedLabel[l - 'a'] = 1;
        i += 2;
    }
}
vector<edge> alledges;

int adjel[MAX_V];
char adje0l[MAX_V];
struct InnerC{
    vector<int> vset;
    vector<int> cut;
    char label;
};
vector<InnerC> AllInnerC;
int innerFlag[MAX_V];
set<int> cutFlag[MAX_V];

void InitialPruning(){
    memset(innerFlag, -1, sizeof(innerFlag));
    int visited[MAX_V];
    memset(visited, 0, sizeof(visited));
    for (int v = 0; v < N;v++){
        int nnei = adjL[v].size();
        for (int i = 0; i < nnei; i++){
            char l = adjL[v][i].label;
            adjel[v] = adjel[v] | (1 << (l - 'a'));
        }
        if (nnei != 0)
            adje0l[v] = adjL[v][0].label;
    }
    for (int i = 0; i < N;i++){
        if(visited[i])
            continue;
        if(adjel[i] == (1 << (adje0l[i] - 'a'))){
            InnerC tmp;
            tmp.vset.push_back(i);
            innerFlag[i] = AllInnerC.size();
            tmp.label = adje0l[i];
            queue<int> bfs4part;
            bfs4part.push(i);
            visited[i] = 1;
            while(bfs4part.size()){
                int v = bfs4part.front();
                bfs4part.pop();
                int nnei = adjL[v].size();
                for (int j = 0; j < nnei;j++){
                    int w = adjL[v][j].to;
                    bool flag = (adjel[w] == (1 << (adje0l[w] - 'a')));
                    if (!visited[w] && flag){
                        bfs4part.push(w);
                        tmp.vset.push_back(w);
                        innerFlag[w] = AllInnerC.size();
                    }
                    if(!flag){
                        tmp.cut.push_back(w);
                        cutFlag[w].insert(AllInnerC.size());
                    }
                    visited[w] = 1;
                }
            }
            AllInnerC.push_back(tmp);
        }
    }
    printf("%d\n", AllInnerC.size());
    size_t mxs = 0, mxbs = 0;
    int ninner = 0, ncut = 0;
    for (int i = 0; i < AllInnerC.size(); i++){
        mxs = max(mxs, AllInnerC[i].vset.size());
        mxbs = max(mxbs, AllInnerC[i].cut.size());
        ncut += AllInnerC[i].cut.size();
        ninner += AllInnerC[i].vset.size();
    }
    printf("%d %d %d %d\n", mxs, mxbs, ninner, N-ninner);
}

struct CCnode{
    vector<int> vset;//no inner
    vector<edge> R[MAX_LS];
    set<int> ladj[MAX_LS];
    bool inR[MAX_LS];
    int vn = 0;
};
vector<CCnode> CCnodes[MAX_LS];
int mnccnodes;
unordered_map<int,int> Nsigma[MAX_V];
long long cachesize;
void save(string filename){
    filename += string("BSMindex");
    ofstream of;
    of.open(filename.c_str(), ios::binary);
    // FILE *fp_index=fopen("index.txt","w");
    // fprintf(fp_index, "%d ", N);
    int tmp = AllInnerC.size();
    of.write(reinterpret_cast<const char *>(&tmp), sizeof(int));
    indexsize++;
    for (int i = 0; i < AllInnerC.size();i++){
        int vs = AllInnerC[i].vset.size(), cs = AllInnerC[i].cut.size();
        of.write(reinterpret_cast<const char *>(&vs), sizeof(int));
        of.write(reinterpret_cast<const char *>(&cs), sizeof(int));
        indexsize += 3 + vs + cs;
        for (int j = 0; j < vs;j++){
            int v = AllInnerC[i].vset[j];
            of.write(reinterpret_cast<const char *>(&v), sizeof(int));
        }
        for (int j = 0; j < cs;j++){
            int v = AllInnerC[i].cut[j];
            of.write(reinterpret_cast<const char *>(&v), sizeof(int));
        }
    }
    for (int i = 0; i < MAX_LS;i++){
        int tmp = CCnodes[i].size();
        if (tmp == 0)
            continue;
        of.write(reinterpret_cast<const char *>(&tmp), sizeof(int));
        indexsize++;
        for (int j = 0; j < tmp;j++){
            CCnode t = CCnodes[i][j];
            int vs = t.vset.size();
            indexsize += 1 + vs;
            of.write(reinterpret_cast<const char *>(&vs), sizeof(int));
            for (int l = 0; l < vs;l++){
                int v = t.vset[l];
                of.write(reinterpret_cast<const char *>(&v), sizeof(int));
            }
            for (int k = 0; k < MAX_LS;k++){
                if(t.R[k].size()){
                    int rk = t.R[k].size();
                    indexsize += 1 + 3 * rk;
                    of.write(reinterpret_cast<const char *>(&rk), sizeof(int));
                    for (int l = 0; l < rk;l++){
                        int v1 = t.R[k][l].from, v2 = t.R[k][l].to;
                        double w1 = t.R[k][l].weight;
                        of.write(reinterpret_cast<const char *>(&v1), sizeof(int));
                        of.write(reinterpret_cast<const char *>(&v2), sizeof(int));
                        of.write(reinterpret_cast<const char *>(&w1), sizeof(int));
                    }
                }
                if(t.ladj[k].size()){
                    int lk = t.ladj[k].size();
                    indexsize += 1 + lk;
                    of.write(reinterpret_cast<const char *>(&lk), sizeof(int));
                    set<int>::iterator it;
                    for (it = t.ladj[k].begin(); it != t.ladj[k].end();it++){
                        int v = *it;
                        of.write(reinterpret_cast<const char *>(&v), sizeof(int));
                    }
                }
            }
        }
    }
    for (int v = 0; v < N;v++){
        unordered_map<int,int>::iterator it;
        for (it = Nsigma[v].begin(); it != Nsigma[v].end();it++){
            indexsize += 2;
            int v1 = it->first, v2 = it->second;
            of.write(reinterpret_cast<const char *>(&v1), sizeof(int));
            of.write(reinterpret_cast<const char *>(&v2), sizeof(int));
        }
    }
    // fclose(fp_index);
    of.close();
}
long long LSDindexsize;
void saveLSD(string filename){
    filename += string("LSDindex");
    ofstream of;
    of.open(filename.c_str(), ios::binary);
    // FILE *fp_index=fopen("index.txt","w");
    // fprintf(fp_index, "%d ", N);
    of.write(reinterpret_cast<const char *>(&N), sizeof(int));
    bfssave.push(root);
    while(!bfssave.empty()){
        int v = bfssave.front();
        bfssave.pop();
        int lenl1 = L[v].size(), nx = T[v].X.size();
        LSDindexsize += 4 + nx;
        //fprintf(fp_index, "%d %d %d %d%c", v, T[v].parent, nx, lenl,' ');
        of.write(reinterpret_cast<const char *>(&v), sizeof(int));
        of.write(reinterpret_cast<const char *>(&T[v].parent), sizeof(int));
        of.write(reinterpret_cast<const char *>(&nx), sizeof(int));
        of.write(reinterpret_cast<const char *>(&lenl1), sizeof(int));
        for (int i = 0; i < nx; i++){
            //fprintf(fp_index, "%d%c", T[v].X[i].first, (i == nx - 1) ? ' ' : ' ');
            of.write(reinterpret_cast<const char *>(&T[v].X[i]), sizeof(int));
        }
        for (int i = 0; i < lenl1; i++){
            int lend = L[v][i].second.size();
            LSDindexsize += 2 + 2 * lend;
            //fprintf(fp_index, "%d %d ", L[v][i].first, lend);
            of.write(reinterpret_cast<const char *>(&L[v][i].first), sizeof(int));
            of.write(reinterpret_cast<const char *>(&lend), sizeof(int));
            for (int q = 0; q < lend;q++){
                of.write(reinterpret_cast<const char *>(&L[v][i].second[q].first), sizeof(int));
                of.write(reinterpret_cast<const char *>(&L[v][i].second[q].second), sizeof(int));
            }
        }
        for (int i = 0; i < T[v].children.size();i++){
            bfssave.push(T[v].children[i]);
        }
    }
    //fclose(fp_index);
    of.close();
}

bool predisflag[MAX_V];
void CCGraphConstruction(){
    int nccv = 0, ncce = 0, maxccv = 0, maxccc = 0;
    for (int c = 0; c < 21;c++){
        int visited[MAX_V];
        for (int v = 0; v < N;v++){
            visited[v] = 0;
        }
        for (int i = 0; i < N; i++)
        {
            if (visited[i])
                continue;
            //printf("start %d:\n", i);
            if (((1 << c) & adjel[i]) == 0)
                continue;
            CCnode tmp;
            queue<int> bfs4part;
            set<int> tvset;
            set<int> groupind;
            bfs4part.push(i);
            while (bfs4part.size())
            {
                int v = bfs4part.front();
                bfs4part.pop();
                visited[v] = 1;
                if (innerFlag[v] == -1)
                    tvset.insert(v);
                for (int j = 0; j < adjL[v].size(); j++)
                {
                    int w = adjL[v][j].to;
                    if (!visited[w] && (adjL[v][j].label - 'a') == c){
                        bfs4part.push(w);
                        visited[w] = 1;
                    }
                }
                if(cutFlag[v].size()){
                    set<int>::iterator it;
                    for (it = cutFlag[v].begin(); it != cutFlag[v].end();it++){
                        int ind = *it;
                        if (AllInnerC[ind].label - 'a' == c)
                            groupind.insert(ind);
                    }
                }
            }
            set<int>::iterator it;
            for (it = groupind.begin(); it != groupind.end(); it++){
                int ind = *it;
                for (int j = 0; j < AllInnerC[ind].vset.size();j++){
                    Nsigma[AllInnerC[ind].vset[j]][c] = CCnodes[c].size();
                }
                tmp.vn += AllInnerC[ind].vset.size();
            }
            for (it = tvset.begin(); it != tvset.end(); it++){
                tmp.vset.push_back(*it);
                Nsigma[*it][c] = CCnodes[c].size();
            }
            maxccv = max(maxccv, (int)tmp.vset.size());
            //tmp.vn += tvset.size();
            set<edge> tmpR[MAX_S];
            for (int j = 0; j < tmp.vset.size();j++){
                int v = tmp.vset[j];
                for (int k = 0; k < adjL[v].size(); k++){
                    int tmplabel = adjL[v][k].label - 'a';
                    tmpR[tmplabel].insert(adjL[v][k]);
                    predisflag[adjL[v][k].to] = 1;
                    predisflag[v] = 1;
                }
            }
            set<edge>::iterator it1;
            for (int j = 0; j < MAX_S;j++){
                tmp.inR[j] = false;
                for (it1 = tmpR[j].begin(); it1 != tmpR[j].end(); it1++)
                {
                    tmp.R[j].push_back(*it1);
                    tmp.inR[j] = true;
                }
            }
            CCnodes[c].push_back(tmp);
        }
        maxccc = max(maxccc, (int)CCnodes[c].size());
        nccv += CCnodes[c].size();
    }
    for (int v = 0; v < N; v++){
        if (innerFlag[v] == -1){
            for (int j = 0; j < adjL[v].size(); j++){
                for (int k = j + 1; k < adjL[v].size(); k++){
                    int c1 = adjL[v][j].label - 'a', c2 = adjL[v][k].label - 'a';
                    if (c1 == c2)
                        continue;
                    if(Nsigma[v].count(c1)&&Nsigma[v].count(c2)){
                        int i1 = Nsigma[v][c1], i2 = Nsigma[v][c2];
                        CCnodes[c1][i1].ladj[c2].insert(i2);
                        CCnodes[c2][i2].ladj[c1].insert(i1);
                    }
                    else{
                        printf("Warning\n");
                    }
                }
            }
        }
    }
    for (int c = 0; c < 21;c++){
        for (int k = 0; k < CCnodes[c].size();k++){
            for (int c2 = 0; c2 < 21;c2++){
                ncce += CCnodes[c][k].ladj[c2].size();
            }
        }
    }
    printf("nccv%d ncce%d %d %d\n", nccv, ncce, maxccv, maxccc);
}

DFA minDfa;
void Reg2minDFA(string str1){
    string oristr = "";
	//transform the label to a letter
    for (int i = 0; i < str1.size();i++){
        if (str1[i] == ' ')
            continue;
        if (str1[i] >= 'A' && str1[i] <= 'D'){
            int cat2 = str1[i + 1] - '0';
            cat2 = (cat2 > 5) ? 5 : cat2;
            char l = (str1[i] - 'A') * 5 + cat2 - 1 + 'a';
            oristr += l;
            i++;
        }
        else
            oristr += str1[i];
    }
    string str = infixToSuffix(oristr);
    int i, j;
	//NFA DFA initialization
	for(i = 0; i < MAX_NS; i++){
		NfaStates[i].index = i;
		NfaStates[i].input = '#';
		NfaStates[i].chTrans = -1;
        NfaStates[i].epTrans.clear();
    }
	for(i = 0; i < MAX_NS; i++){
		DfaStates[i].index = i;
		DfaStates[i].isEnd = false;
        DfaStates[i].edgeNum = 0;
        DfaStates[i].closure.clear();
        for(j = 0; j < MAX_LS; j++){
			DfaStates[i].Edges[j].input = '#';
			DfaStates[i].Edges[j].Trans = -1;
		}
	}
	for(i = 0; i < MAX_NS; i++){
		minDfaStates[i].index = i;
		minDfaStates[i].isEnd = false;
        minDfaStates[i].edgeNum = 0;
        minDfaStates[i].closure.clear();
        for(int j = 0; j < MAX_LS; j++)
		{
			minDfaStates[i].Edges[j].input = '#';
			minDfaStates[i].Edges[j].Trans = -1;
		}
	}
    minDfa.endStates.clear();
    minDfa.startState = -1;
    minDfa.terminator.clear();
    for(i = 0; i < MAX_NS; i++){
        for(int j = 0; j < 26; j++)
		{
            minDfa.trans[i][j] = -1;
        }
	}
    nfaStateNum = 0;
    minDfaStateNum = 0;
    for (i = 0; i < MAX_NS;i++)
		s[i].clear();

    NFA n = strToNfa(str);//string to NFA
    //printNFA(n);
	DFA d = nfaToDfa(n, str);//NFA to DFA
	//printDFA(d);
	minDfa = minDFA(d);//DFA minimization
	//printMinDFA(minDfa);
    string teststr = "bbbpppppp";
    printf("%s: %d DFA states\n", oristr.c_str(), minDfaStateNum);
    //printf("%s test:%d\n", teststr.c_str(), indicator(minDfa, teststr));
}

struct grid{
    int center;
    vector<int> vert;
    vector<double> vcdis;
    vector<double> cbdis;
};
grid grids[450][450];
int ngridx, ngridy;
II coords2ind[MAX_V];
int coords2indInside[MAX_V];
int mapbor2ind[MAX_V];
double griddis[2510][2510];

double priobor(int v,int b){
    int indx = coords2ind[v].first, indy = coords2ind[v].second;
    int indin = coords2indInside[v];
    double d1 = grids[indx][indy].vcdis[indin];
    int indb = mapbor2ind[b];
    double d2 = grids[indx][indy].cbdis[indb];
    return abs(d2 - d1);
}
double gridlb(int v, int u){
    int indx = coords2ind[v].first, indy = coords2ind[v].second;
    int indin = coords2indInside[v];
    double d1 = grids[indx][indy].vcdis[indin];
    int indx2 = coords2ind[u].first, indy2 = coords2ind[u].second;
    int indin2 = coords2indInside[u];
    double d2 = grids[indx2][indy2].vcdis[indin2];
    double d3 = griddis[indx + indy * ngridx][indx2 + indy2 * ngridx];
    return abs(abs(d3 - d1) - d2);
}

double prio(int v,int t){
    return gridlb(v, t);
    return calculateDistance(v, t);
    double mret = -1;
    for (int i = 0; i < nlm;i++)
        mret = max(mret, abs(lm[v][i] - lm[t][i]));
    return mret;
}
double df[MAX_V][MAX_S], db[MAX_V][MAX_S];
vector<int> selflabels[MAX_S], outlabels[MAX_S], outlabelsrev[MAX_S];
settype Lself[MAX_S], Lmove[MAX_S], Lrem[MAX_S], Lremrev[MAX_S];
bool cmpedge(const edge &e1, const edge &e2){
    return e1.tldis12 < e2.tldis12;
}
bool samecc(int s, int t, settype self){
    if(self==0)
        return 0;
    int i = logn2[self];
    if(i!=-1){
        if (Nsigma[s].count(i) && Nsigma[t].count(i) && Nsigma[s][i] == Nsigma[t][i])
            return true;
        else
            return false;
    }
    return ccquery(s, t, self);
}
typedef struct pqn{
	double Aw;
    double w;
    int v;
    int q;
    pqn(double _Aw, int _v,int _q, double _w){
        Aw = _Aw, w = _w, v = _v, q = _q;
    }
};
struct cmppqn{
    bool operator()(const pqn &a, const pqn &b){
        return a.Aw > b.Aw;
    }
};
int DFAq0;
vector<int> rtrans[MAX_S][26];
unordered_map<int,int> regadj[MAX_S], regradj[MAX_S];
double biBFS(int s, int t){
    double ub = DBL_MAX, mu = DBL_MAX;
    if (finalFlag[DFAq0]){
        if (Lself[DFAq0] != 0 && samecc(s, t, Lself[DFAq0])){
            double dis = LSDQuery(s, t, Lself[DFAq0]);
            if (minDfaStateNum == 1)
                return dis;
            mu = min(mu, dis);
            df[t][DFAq0] = min(df[t][DFAq0], mu);
            db[s][DFAq0] = min(db[s][DFAq0], mu);
        }
    }
    vector<int> fv[MAX_S], bv[MAX_S];
    priority_queue<pqn, vector<pqn>, cmppqn> Qfb, Qfq;
    Qfq.push(pqn(0, s, DFAq0, 0));
    fv[DFAq0].push_back(s);
    for (int i = MAX_S - 1; i >=0 ;i--)
        if(finalFlag[i]){
            db[t][i] = 0;
            Qfb.push(pqn(0, t, i, 0));
            bv[i].push_back(t);
        }
    double lastqf = 0, lastqb = 0;
    while (!Qfq.empty()&&!Qfb.empty()){
        pqn qfu = Qfq.top(), qfb = Qfb.top();
        Qfq.pop();Qfb.pop();
        while (!Qfq.empty()&&df[qfu.v][qfu.q] < qfu.w){
            qfu = Qfq.top();
            Qfq.pop();
        }
        while (!Qfb.empty()&&db[qfb.v][qfb.q] < qfb.w){
            qfb = Qfb.top();
            Qfb.pop();
        }
        int v = qfu.v, q = qfu.q;
        int vb = qfb.v, qb = qfb.q;
        if (q == qb){
            if(Lself[q]!=0 && samecc(v, vb, Lself[q])){
                double dis = LSDQuery(v, vb, Lself[q]);
                mu = min(mu, dis + df[v][q] + db[vb][qb]);
                df[vb][qb] = min(df[vb][qb], df[v][q] + dis);
                db[v][q] = min(db[v][q], db[vb][qb] + dis);
            }
        }
        if(df[v][q]+prio(v,t)<=mu){
        //forward
        bool noborderflag = false;
        if (Lself[q] != 0 && Lmove[q] != 0){
            queue<II> bfscc;
            for (int i = 0; i < selflabels[q].size(); i++){
                int c = selflabels[q][i];
                if (Nsigma[v].count(c))
                    bfscc.push(II(c, Nsigma[v][c]));
            }
            if(bfscc.size())
                noborderflag = false;
            else
                noborderflag = true;
            set<int> visited[26];
            set<int> vis;
            while (bfscc.size()){
                int i1 = bfscc.front().first, i2 = bfscc.front().second;
                bfscc.pop();
                if(visited[i1].count(i2))
                    continue;
                visited[i1].insert(i2);
                for (int j = 0; j < outlabels[q].size(); j++){
                    int indj = outlabels[q][j], nR = CCnodes[i1][i2].R[indj].size();
                    for (int k = 0; k < nR; k++){
                        edge e = CCnodes[i1][i2].R[indj][k];
                        if(vis.count(e.id))
                            continue;
                        int u = e.from;
                        double ut = priobor(t, u);
                        if (df[v][q] + priobor(v, u) +  ut> mu)
                            continue;
                        double dis = LSDQuery(v, u, Lself[q]);
                        if (df[v][q] + dis + ut > mu)
                            continue;                        
                        if ((df[u][q] >= df[v][q] + dis) || (dis == 0)){
                            df[u][q] = df[v][q] + dis;
                            mu = min(mu, df[u][q] + db[u][q]);
                            int eto = e.to, toq = minDfa.trans[q][e.label - 'a'];
                            if (toq == -1 || toq == q)
                                continue;
                            if (df[eto][toq] > df[u][q] + e.weight){
                                df[eto][toq] = df[u][q] + e.weight;
                                mu = min(mu, df[eto][toq] + db[eto][toq]);
                                double lbdis = prio(eto, t);
                                if (df[eto][toq] + lbdis < mu){
                                    Qfq.push(pqn(df[eto][toq], eto, toq, df[eto][toq]));
                                }
                            }
                        }
                        vis.insert(e.id);
                    }
                }
                for (int j = 0; j < selflabels[q].size(); j++){
                    int qj = selflabels[q][j];
                    if (i1 != qj){
                        set<int>::iterator it;
                        for (it = CCnodes[i1][i2].ladj[qj].begin(); it != CCnodes[i1][i2].ladj[qj].end(); it++){
                            if(visited[qj].count(*it)==0)
                                bfscc.push(II(qj, *it));
                        }
                    }
                }
            }
            if(noborderflag){
                if(finalFlag[q]){
                    double dis = LSDQuery(v, t, Lself[q]);
                    mu = min(mu, df[v][q] + dis);
                    df[t][q] = min(df[t][q], df[v][q] + dis);
                }
            }        
        }
        if (Lmove[q] != 0 && Lself[q] == 0){
            int u = v;
            for (int i = 0; i < adjL[u].size();i++){
                int eto = adjL[u][i].to;
                edge e = adjL[u][i];
                int toq = minDfa.trans[q][e.label - 'a'];
                if (toq == -1 || toq == q)
                    continue;
                if (df[eto][toq] > df[u][q] + e.weight){
                    df[eto][toq] = df[u][q] + e.weight;
                    mu = min(mu, df[eto][toq] + db[eto][toq]);
                    double lbdis = prio(eto, t);
                    if (df[eto][toq] + lbdis < mu){
                        Qfq.push(pqn(df[eto][toq], eto, toq, df[eto][toq]));
                    }
                }
            }
        }
        }
        if (db[vb][qb] + prio(vb, s) <= mu){
        //backward
        bool noborderflag = false;
        if (Lself[qb] != 0 && outlabelsrev[qb].size() != 0){
            queue<II> bfscc;
            for (int i = 0; i < selflabels[qb].size(); i++){
                int c = selflabels[qb][i];
                if (Nsigma[vb].count(c))
                    bfscc.push(II(c, Nsigma[vb][c]));
            }
            if(bfscc.size())
                noborderflag = false;
            else
                noborderflag = true;
            set<int> visited[MAX_S];
            set<int> vis;
            while (bfscc.size()){
                int i1 = bfscc.front().first, i2 = bfscc.front().second;
                bfscc.pop();
                if(visited[i1].count(i2))
                    continue;
                visited[i1].insert(i2);
                for (int j = 0; j < outlabelsrev[qb].size(); j++){
                    int indj = outlabelsrev[qb][j], nR = CCnodes[i1][i2].R[indj].size();
                    for (int k = 0; k < nR;k++){
                        edge e = CCnodes[i1][i2].R[indj][k];
                        if(vis.count(e.id))
                            continue;
                        int eto, u;
                        int b = e.from;
                        double sb = priobor(s, b);
                        if (db[vb][qb] + priobor(vb, b) + sb > mu)
                            continue;
                        double latdis = 0;
                        if(((Lself[qb]>>(e.label-'a'))&1))
                            eto = e.from, u = e.to, latdis = abs(sb - e.weight);
                        else
                            eto = e.to, u = e.from, latdis = sb;
                        double dis = LSDQuery(vb, u, Lself[qb]);
                        if (db[vb][qb] + dis + latdis > mu)
                            continue;
                        if ((db[u][qb] >= db[vb][qb] + dis) || (dis == 0)){
                            db[u][qb] = db[vb][qb] + dis;
                            mu = min(mu, df[u][qb] + db[u][qb]);
                            for (int l = 0; l < rtrans[qb][e.label - 'a'].size();l++){
                                int toq = rtrans[qb][e.label - 'a'][l];
                                if (toq == -1 || toq == qb)
                                    continue;
                                if (db[eto][toq] > db[u][qb] + e.weight){
                                    db[eto][toq] = db[u][qb] + e.weight;
                                    mu = min(mu, df[eto][toq] + db[eto][toq]);
                                    double lbdis = prio(eto, s);
                                    if (lbdis + db[eto][toq] < mu){
                                        Qfb.push(pqn(db[eto][toq], eto, toq, db[eto][toq]));
                                    }
                                }
                            }
                        }
                        vis.insert(e.id);
                    }
                }
                for (int j = 0; j < selflabels[qb].size(); j++){
                    int qj = selflabels[qb][j];
                    if (i1 != qj){
                        set<int>::iterator it;
                        for (it = CCnodes[i1][i2].ladj[qj].begin(); it != CCnodes[i1][i2].ladj[qj].end(); it++){
                            if(visited[qj].count(*it)==0)
                                bfscc.push(II(qj, *it));
                        }
                    }
                }
            }
            if(noborderflag){
                if(qb==DFAq0){
                    double dis = LSDQuery(vb, s, Lself[qb]);
                    mu = min(mu, db[vb][qb] + dis);
                    db[s][qb] = min(db[s][qb], db[vb][qb] + dis);
                }
            }        
        }
        if (outlabelsrev[qb].size() != 0 && Lself[qb] == 0){
            int u = vb;
            for (int i = 0; i < adjL[u].size();i++){
                int eto = adjL[u][i].to;
                edge e = adjL[u][i];
                for (int l = 0; l < rtrans[qb][e.label - 'a'].size();l++){
                    int toq = rtrans[qb][e.label - 'a'][l];
                    if (toq == -1 || toq == qb)
                        continue;
                    if (db[eto][toq] > db[u][qb] + e.weight){
                        db[eto][toq] = db[u][qb] + e.weight;
                        mu = min(mu, df[eto][toq] + db[eto][toq]);
                        double lbdis = prio(eto, s);
                        if (lbdis + db[eto][toq] < mu){
                            Qfb.push(pqn(db[eto][toq], eto, toq, db[eto][toq]));
                        }
                    }
                }
            }
        }
        }

        if (df[v][q] + db[vb][qb] >= mu)
            return mu;
    }

    if(mu==DBL_MAX)
        return -1;
    return mu;
}

double BSMQuery(int s, int t, string regL, bool fixLflag){
    s--, t--;
    if(!fixLflag){
        Reg2minDFA(regL);
        DFAq0 = minDfa.startState;
        bool visoutlabel[MAX_S][26], visselflabel[MAX_S][26];
        for(int i = 0; i < MAX_S; i++){
            regadj[i].clear();
            regradj[i].clear();
            selflabels[i].clear();
            outlabels[i].clear();
            outlabelsrev[i].clear();
        }
        for(int i = 0; i < MAX_S; i++){
            Lself[i] = Lmove[i] = Lrem[i] = Lremrev[i] = 0;
            for(int j = 0; j < 26; j++){
                rtrans[i][j].clear();
                visoutlabel[i][j] = visselflabel[i][j] = 0;
            }
        }
        for(int i = 0; i < MAX_S; i++){
            for(int j = 0; j < 26; j++){
                int toS = minDfa.trans[i][j];
                if(toS != -1){
                    rtrans[toS][j].push_back(i);
                    if(toS==i){
                        Lself[i] = Lself[i] | (1 << j);
                        selflabels[i].push_back(j);
                        visselflabel[i][j] = 1;
                    }
                    else{
                        Lmove[i] = Lmove[i] | (1 << j);
                        outlabels[i].push_back(j);
                        if(!visoutlabel[toS][j]){
                            outlabelsrev[toS].push_back(j);
                            visoutlabel[toS][j] = 1;
                        }
                        regadj[i][toS] = j;
                        regradj[toS][i] = j;
                    }
                }
                Lrem[i] = Lremrev[i] = Lself[i];
            }
        }
    }
    if (s == t)
        return 0;
    df[s][DFAq0] = 0;
    return biBFS(s, t);
}

int cntlabel[MAX_S];
void rep(string qi, string sfile, string &setres, string reg, bool fixflag){
    std::chrono::high_resolution_clock::time_point t1, t2;
	std::chrono::duration<double> time_span;
    vector<II> queryset;
    vector<string> rega;
    vector<double> ans;
    string s3 = string("../data/") + sfile + string("/") + qi;
    FILE *fp_query = fopen(s3.c_str(), "r");
    int qs, qt;
    if(fixflag){
        while (~fscanf(fp_query, "%d%d", &qs, &qt)){
            queryset.push_back(II(qs, qt));
        }
        BSMQuery(1, 1, reg, 0);
    }
    else{
        char regarray[200];
        while (~fscanf(fp_query, "%d%d%s", &qs, &qt, regarray)){
            queryset.push_back(II(qs, qt));
            rega.push_back(string(regarray));
        }
    }
    fclose(fp_query);
    int qn = queryset.size();
    double runT = 0;
    for (int i = 0; i < qn; i++){
        for (int ki = 0; ki <= N;ki++){
            for (int j = 0; j < MAX_S;j++){
                df[ki][j] = db[ki][j] = DBL_MAX;
            }
        }
        double tmp;
        if(fixflag){
            t1=std::chrono::high_resolution_clock::now();
            tmp = BSMQuery(queryset[i].first, queryset[i].second, reg, 1);
            t2=std::chrono::high_resolution_clock::now();
        }
        else{
            t1=std::chrono::high_resolution_clock::now();
            tmp = BSMQuery(queryset[i].first, queryset[i].second, rega[i], 0);
            t2=std::chrono::high_resolution_clock::now();
        }
        time_span = std::chrono::duration_cast<std::chrono::duration<double>>(t2-t1);
        runT += time_span.count();
        ans.push_back(tmp);
    }        
    cout << (qi).c_str() << " Query Time " << runT*1000 << endl;
    setres += (qi);
    setres += string(" Query Time \n") + to_string(runT*1000) + string("\n");

    FILE *fp_out = fopen((s3+string("BSMResults")).c_str(), "w");
    for (int i = 0; i < ans.size(); i++)
        fprintf(fp_out, "%f\n", ans[i]);
    fclose(fp_out);
    setres += string("\n");
}

void preprocesslbdis(){
    int nn = 0,maxnn=0;
    for (int i = 0; i < ngridx;i++){
        for (int j = 0; j < ngridy;j++){
            nn += grids[i][j].vert.size();
            maxnn = max(maxnn, (int)grids[i][j].vert.size());
            if(grids[i][j].vert.size()==0){
                grids[i][j].center = -1;
                continue;
            }
            int cent = grids[i][j].center;
            for (int k = 0; k < grids[i][j].vert.size();k++){
                grids[i][j].vcdis.push_back(h2hQuery(cent, grids[i][j].vert[k], 0));
            }
        }
    }
    int nbor = 0;
    for (int v = 0;v<N;v++){
        mapbor2ind[v] = -1;
        if(innerFlag[v]==-1){
            mapbor2ind[v] = nbor++;
        }
    }
    printf("%d %d %d %d %d\n", ngridx, ngridy, nn, maxnn, nbor);
    for (int i = 0; i < ngridx;i++){
        for (int j = 0; j < ngridy;j++){
            if(grids[i][j].vert.size()==0)
                continue;
            int cent = grids[i][j].center;
            for (int v = 0;v<N;v++){
                if(innerFlag[v]==-1){
                    grids[i][j].cbdis.push_back(h2hQuery(cent, v, 0));
                }
            }
        }
    }

    for (int i = 0; i < ngridx;i++){
        for (int j = 0; j < ngridy;j++){
            if(grids[i][j].vert.size()==0)
                continue;
            int cent = grids[i][j].center;
            for (int i1 = 0; i1 < ngridx;i1++){
                for (int j1 = 0; j1 < ngridy;j1++){
                    if(grids[i1][j1].vert.size()==0)
                        continue;
                    int cent1 = grids[i1][j1].center;
                    griddis[i + j * ngridx][i1 + j1 * ngridx] = h2hQuery(cent, cent1, 0);
                }
            }
        }
    }
}

int main(int argc , char * argv[]){
    string sfile, sq, srandom, sreg;
    FILE *fp_query, *fp_network;
    double sl;
    if (argc > 1)
        sfile = string(argv[1]);
    else
        sfile = string("NYC");
    if (argc > 2)
        sq = string(argv[2]);
    else
        sq = string("q1");
    if (argc > 3)
        sreg = string(argv[3]);
    else
        sreg = string("D1*");

    string prefix = string("../data/") + sfile + string("/");
    string graphfile = prefix + string("USA-road-l.") + sfile + (".gr");
    fp_network = fopen(graphfile.c_str(), "r");
    char ch, buffer[100];
    int u, v, cat2;
    double w;
    char cat1;
    //read graph
    for (int i = 0; i < 4; i++)
        fgets(buffer, 90, fp_network);
    for (int i = 0; i < 4; i++)
        fgetc(fp_network);
    fscanf(fp_network, "%d%d", &N, &M);
    for (int i = 0; i < 3; i++)
        fgets(buffer, 90, fp_network);
    for (int i = 0; i < M; i++) {
        fscanf(fp_network, "%c%d%d%lf%c%c%d", &ch, &u, &v, &w, &cat1, &cat1, &cat2);
        fgets(buffer, 90, fp_network);
        u--;
        v--;
        cat2 = (cat2 > 5) ? 5 : cat2;
        char l = (cat1 - 'A') * 5 + cat2 - 1 + 'a';
        //printf("%d %d %c%d %c\n", u, v, cat1, cat2, l);
        if (i % 2 == 0){
            adjo[u][v] = 1;
            adjo[v][u] = 1;
            adjL[u].push_back(edge(u, v, w, l));
            adjL[v].push_back(edge(v, u, w, l));
            adjL[u][adjL[u].size() - 1].id = i;
            adjL[v][adjL[v].size() - 1].id = i + 1;
            alledges.push_back(edge(u, v, w, l));
            cntlabel[l - 'a']++;
        }
    }
    double minx = DBL_MAX, miny = DBL_MAX, maxx = -DBL_MAX, maxy = -DBL_MAX;
    if(1){
        //coords
        string coordsfile = prefix + string("USA-road-d.") + sfile + (".co");
        FILE *fp_coords = fopen(coordsfile.c_str(), "r");
        for (int i = 0; i < 7; i++)
            fgets(buffer, 90, fp_coords);
        
        for (int i = 0; i < N; i++) {
            double x, y;
            fscanf(fp_coords, "%c%d%lf%lf", &ch, &u, &x, &y);
            fgets(buffer, 90, fp_coords);
            x /= 1000000.0;
            y /= 1000000.0;
            coords.push_back(DD(x, y));
            minx = min(x, minx), miny = min(y, miny), maxx = max(x, maxx), maxy = max(y, maxy);
        }
    }
    printf("%f %f %f %f\n", minx, maxx, miny, maxy);

    memset(coords2indInside, -1, sizeof(coords2indInside));
    double lengrid = 0.02; // 0.005
    for (int i = 0; i < N; i++) {
        double x = coords[i].first, y = coords[i].second;
        int indx = (x - minx) / lengrid, indy = (y - miny) / lengrid;
        grids[indx][indy].vert.push_back(i);
        coords2indInside[i] = grids[indx][indy].vert.size() - 1;
        grids[indx][indy].center = i;
        coords2ind[i] = II(indx, indy);
        ngridx = max(ngridx, indx);
        ngridy = max(ngridy, indy);
    }
    ngridx++, ngridy++;

    std::chrono::high_resolution_clock::time_point t1, t2;
	std::chrono::duration<double> time_span;
	double runT;
    string setres=sfile+string("\n");

    t1=std::chrono::high_resolution_clock::now();
    string ordername = string("../data/") + sfile + string("/") + string("order.txt");
    if(0){//generate order for vertices
        genorder(ordername, 1);
    }
    else{//get order from file
        ordergen.assign(N, -1);
        FILE *fpord = fopen(ordername.c_str(), "r");
        for (int i = 0; i < N; i++){
            fscanf(fpord, "%d", &T[i].ran);
            ordergen[T[i].ran] = i;
        }
    }
    t2 = std::chrono::high_resolution_clock::now();
    time_span = std::chrono::duration_cast<std::chrono::duration<double>>(t2-t1);
	runT= time_span.count();
	cout<<"Order Generation Time "<<runT<<endl;

    // distribute edges
    for (int i = 0; i < alledges.size(); i++)
    {
        int f = alledges[i].from, t = alledges[i].to;
        double w = alledges[i].weight;
        if(T[f].ran>T[t].ran)
            swap(f, t);
        adjT[f][t] = 1;
        adj[f][t][1 << (alledges[i].label - 'a')] = w;
    }

    priority_queue<II> pql;
    for (int i = 0; i < 26;i++)
        if(cntlabel[i])
            pql.push(II(cntlabel[i], i));
    int nmaplabel = min((int)pql.size(), 10);
    for (int i = 0; i < nmaplabel;i++){
        maplabel[pql.top().second] = i + 1;
        //printf("%d %d\n", pql.top().second, i + 1);
        pql.pop();
    }

    memset(logn2, -1, sizeof(logn2));
    logn2[1] = 0;
    int val = 1;
    for (int i = 0; i < 27;i++){
        logn2[val] = i;
        val *= 2;
    }

    t1 = std::chrono::high_resolution_clock::now();
    InitialPruning();
    t2=std::chrono::high_resolution_clock::now();
    time_span = std::chrono::duration_cast<std::chrono::duration<double>>(t2-t1);
	runT= time_span.count();
    cout << "Initial Pruning Time " << runT << endl;
    setres += string("Initial Pruning Time ") + to_string(runT) + string("\n");

    t1 = std::chrono::high_resolution_clock::now();
    CCGraphConstruction();
    t2=std::chrono::high_resolution_clock::now();
    time_span = std::chrono::duration_cast<std::chrono::duration<double>>(t2-t1);
	runT= time_span.count();
    cout << "CC Graph Construction Time " << runT << endl;
    setres += string("CC Graph Construction Time ") + to_string(runT) + string("\n");

    t1 = std::chrono::high_resolution_clock::now();
    //FILE *fp = fopen("BSMindex", "w");
    save(string("../data/") + sfile + string("/"));// test without save
    t2=std::chrono::high_resolution_clock::now();
    time_span = std::chrono::duration_cast<std::chrono::duration<double>>(t2-t1);
	runT= time_span.count();
    cout << "Saving Time " << runT << endl;
    cout << "Index Size " << (double)indexsize * 4 / 1000000 << "MB" << endl;
    setres += string("Saving Time ") + to_string(runT) + string("\n");
    setres += string("Index Size ") + to_string((double)indexsize * 4 / 1000000) + string("MB\n");

    t1=std::chrono::high_resolution_clock::now();
    P2H();
    t2=std::chrono::high_resolution_clock::now();
    time_span = std::chrono::duration_cast<std::chrono::duration<double>>(t2-t1);
	runT= time_span.count();
	cout<<"P2H Time "<<runT<<endl;
    setres += string("P2H Time ") + to_string(runT)+ string("\n");

    t1=std::chrono::high_resolution_clock::now();
    treedec();
    t2=std::chrono::high_resolution_clock::now();
    time_span = std::chrono::duration_cast<std::chrono::duration<double>>(t2-t1);
	runT= time_span.count();
	cout<<"Tree Decomposition Time "<<runT<<endl;
    cout << "Tree Width " << treewidth << endl;
    setres += string("Tree Decomposition Time ") + to_string(runT)+ string("\n");

    lcamain();

    t1=std::chrono::high_resolution_clock::now();
    labeling();
    t2=std::chrono::high_resolution_clock::now();
    time_span = std::chrono::duration_cast<std::chrono::duration<double>>(t2-t1);
	runT= time_span.count();
	cout<<"Labeling Time "<<runT<<endl;
    cout << "Tree Avg. Height " << treeavgheight / N << endl;
    cout << "Max. Label Size " << maxlabelsize << endl;
    cout << "Avg. Label Size " << (double)avglabelsize / treeavgheight << endl;
    setres += string("Labeling Time ") + to_string(runT) + string("\n");
    setres += string("Tree Width ") + to_string(treewidth) + string("\n");    
    setres += string("Max. Label Size ") + to_string(maxlabelsize) + string("\n");
    setres += string("Avg. Label Size ") + to_string((double)avglabelsize / treeavgheight) + string("\n");

    t1=std::chrono::high_resolution_clock::now();
    preprocesslbdis();
    t2=std::chrono::high_resolution_clock::now();
    time_span = std::chrono::duration_cast<std::chrono::duration<double>>(t2-t1);
	runT= time_span.count();
	cout<<"Preprocesslbdis Time "<<runT<<endl;
    setres += string("Preprocesslbdis Time ") + to_string(runT)+ string("\n");

    t1 = std::chrono::high_resolution_clock::now();
    //FILE *fp = fopen("LSDindex", "w");
    saveLSD(string("../data/") + sfile + string("/"));// test without save
    t2=std::chrono::high_resolution_clock::now();
    time_span = std::chrono::duration_cast<std::chrono::duration<double>>(t2-t1);
	runT= time_span.count();
    cout << "Saving LSD Index Time " << runT << endl;
    cout << "LSD Index Size " << (double)LSDindexsize * 4 / 1000000 << "MB" << endl;
    setres += string("Saving LSD Index Time ") + to_string(runT) + string("\n");
    setres += string("LSD Index Size ") + to_string((double)LSDindexsize * 4 / 1000000) + string("MB\n");

    if (argc > 3){
        setres += sreg + string(":\n");
        rep(sq, sfile, setres, sreg, 1);
    }
    else{
        setres += sreg + string(":\n");
        rep(sq, sfile, setres, sreg, 0);
    }

    FILE *fp_record = fopen("BSMRecord.txt", "a");
    fprintf(fp_record, "%s\n", setres.c_str());
    fclose(fp_record);
    return 0;
}