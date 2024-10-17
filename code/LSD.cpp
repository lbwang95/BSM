#include<bits/stdc++.h>
#include<unordered_map>
using namespace std;
#define settype int
typedef pair<double, int> DI;
typedef pair<int, int> II;
typedef unordered_map<settype, double> USD;
typedef pair<settype, double> SD;
typedef pair<int, vector<SD>> IV;
const int MAX_V = 1070386;
int N, M;//# of vertices and edges
long long hopsize, npathConcat;//# of path concatenations
double optw = DBL_MAX;//optimal answer
int treeheight = 0, treewidth = 0, treeavgheight = 0;

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
vector<IV> L[MAX_V];//supersets
vector<int> anc[MAX_V];
int root = -1;
unordered_map<int, USD> adj[MAX_V];//contains only edges to higher rank
//unordered_map<int, double> adju[MAX_V];//contains only edges to higher rank
unordered_map<int,int> adjo[MAX_V], adjT[MAX_V];//contains all the edges
vector<edge> adjL[MAX_V];
int allowedLabel[100];
settype allowedLabels;
int nsym;

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
        for (it = adj[v][u].begin(); it != adj[v][u].end();it++){
            int s1 = it->first;
            double dis = it->second;
            tmp.push_back(SD(s1, dis));
        }
        sort(tmp.begin(), tmp.end(), cmpSD);
        L[v].push_back(make_pair(u, tmp));
        maxlabelsize = max(maxlabelsize, (double)tmp.size());
        avglabelsize += (double)tmp.size();
        //printf("%d %d:\n", v+1,u+1);
        //printSD(tmp);
    }
    vector<SD> tmp;
    L[v].push_back(make_pair(v, tmp));
    ancarray[v].push_back(lenanc);
    totalwidth += T[v].X.size();
    //printf("\nLvsize%d %d\n", L[v].size(),Lu[v].size());
}
void labeling(){
    //label in a top-down manner
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
    /*for (int i = 1; i < N + 1; i++){
        addEdge(i, T[i-1].parent+1);
    }
    precompute_lca(N);*/
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

unordered_map<int, unordered_map<int, double>> cachedis[MAX_V];
long long hittimes, alltimes;
double dist(int u, int ind, settype s){
    for (int i = 0; i < L[u][ind].second.size(); i++){
        settype s1 = L[u][ind].second[i].first;
        if ((s1 & s) == s1)
            return L[u][ind].second[i].second;
    }
    return DBL_MAX;
}
double LSDQuery(int s, int t){
    optw = DBL_MAX;
    s--, t--;
    if (s == t)
        return 0;
    if (s > t)
        swap(s, t);
    int l = LCA(s + 1, t + 1) - 1, ind;
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
    if(optw==DBL_MAX)
        return -1;
    return optw;
}

void setLabels(string regL){
    allowedLabels = 0;
    nsym = 0;
    for (int i = 0; i < 100;i++)
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
        setLabels(reg);
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
        double tmp;
        if(fixflag){
            t1=std::chrono::high_resolution_clock::now();
            tmp = LSDQuery(queryset[i].first, queryset[i].second);
            t2=std::chrono::high_resolution_clock::now();
        }
        else{
            t1=std::chrono::high_resolution_clock::now();
            setLabels(rega[i]);
            tmp = LSDQuery(queryset[i].first, queryset[i].second);
            t2=std::chrono::high_resolution_clock::now();
        }
        time_span = std::chrono::duration_cast<std::chrono::duration<double>>(t2-t1);
        runT += time_span.count();
        ans.push_back(tmp);
    }        
    cout << (qi).c_str() << " Query Time " << runT*1000 << endl;
    setres += (qi);
    setres += string(" Query Time \n") + to_string(runT*1000) + string("\n");

    FILE *fp_out = fopen((s3+string("LSDResults")).c_str(), "w");
    for (int i = 0; i < ans.size(); i++)
        fprintf(fp_out, "%f\n", ans[i]);
    fclose(fp_out);
}

int main(int argc , char * argv[]){
    string sfile, sq, srandom, sreg;
    FILE *fp_query, *fp_network;
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
            alledges.push_back(edge(u, v, w, l));
        }
    }

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
        //printf("%d %d:\n", f + 1, t + 1);
        //printUSD(adj[f][t]);
    }


    t1=std::chrono::high_resolution_clock::now();
    treedec();
    t2=std::chrono::high_resolution_clock::now();
    time_span = std::chrono::duration_cast<std::chrono::duration<double>>(t2-t1);
	runT= time_span.count();
	cout<<"Tree Decomposition Time "<<runT<<endl;
    cout << "Tree Width " << treewidth << endl;
    setres += string("Tree Decomposition Time ") + to_string(runT)+ string("\n");

    lcamain();
    cout<<"lcamain Finished "<<endl;

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

    t1 = std::chrono::high_resolution_clock::now();

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

    FILE *fp_record = fopen("LSDRecord.txt", "a");
    fprintf(fp_record, "%s\n", setres.c_str());
    fclose(fp_record);
    return 0;
}