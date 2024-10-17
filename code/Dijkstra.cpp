#include<bits/stdc++.h>
#include "Regex2MinDFA.h"
#include<unordered_map>
using namespace std;
#define settype int
typedef pair<double, int> DI;
typedef pair<int, int> II;
typedef unordered_map<settype, double> USD;
typedef pair<settype, double> SD;
typedef pair<int, vector<SD>> IV;
const int MAX_V = 1070386;
int N, M;
double optw = DBL_MAX;//optimal answer

struct edge{
    int from, to;
    double weight;
    char label;
    edge(int a,int b,double w,char l){
        from = a, to = b, weight = w, label = l;
    }
};
vector<edge> adjL[MAX_V];
int nsym;

void printset(settype a){
    int i = 0;
    while(a>0){
        if(a&1)
            printf("%c ", 'a'+i);
        i += 1;
        a = a >> 1;
    }
    cout << endl;
}
void printUSD(USD a){
    USD::iterator it;
    for (it = a.begin(); it != a.end(); it++){
        printset(it->first);
        printf("%f\n", it->second);
    }
}
void printSD(vector<SD> a){
    for (int i = 0; i < a.size();i++){
        printset(a[i].first);
        printf("%f\n", a[i].second);
    }
}

vector<edge> alledges;
DFA minDfa;
void Reg2minDFA(string str1){
	//string str = "(a|b)*abb";
	//string str = "(a|b)*c|z*";
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

double df[MAX_V][MAX_S];
II pre[MAX_V][MAX_S];

typedef struct pqn{
    double w;
    int v;
    int q;
    pqn(double _w, int _v,int _q){
        w = _w, v = _v, q = _q;
    }
};
struct cmppqn{
    bool operator()(const pqn &a, const pqn &b){
        return a.w > b.w;
    }
};
typedef pair<double, char> DC;
unordered_map<int, DC> adj[MAX_V];
double DijkstraQuery(int s, int t, string regL, bool fixLflag){
    s--, t--;
    if(!fixLflag)
        Reg2minDFA(regL);
    if (s == t)
        return 0;
    int DFAq0 = minDfa.startState;
    priority_queue<pqn, vector<pqn>, cmppqn> Qf;
    df[s][DFAq0] = 0;
    Qf.push(pqn(0, s, DFAq0));
    double mu = DBL_MAX, ub = DBL_MAX;
    pre[s][DFAq0] = II(-1, -1);
    while (!Qf.empty()){
        pqn qfu = Qf.top();
        Qf.pop();
        int v = qfu.v;
        int q = qfu.q;
        if (df[v][q] < qfu.w)
            continue;
        if (finalFlag[q]){
            if (v == t){
                return df[t][q];
            }
        }
        for (int i = 0; i < adjL[v].size();i++){
            edge e = adjL[v][i];
            int toq = minDfa.trans[q][e.label - 'a'];
            if (toq == -1)
                continue;
            if (df[e.to][toq] > df[v][q] + e.weight){
                df[e.to][toq] = df[v][q] + e.weight;
                pre[e.to][toq] = II(v, q);
                Qf.push(pqn(df[e.to][toq], e.to, toq));
            }
        }
    }
    return -1;
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
        DijkstraQuery(1, 1, reg, 0);
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
                df[ki][j] = DBL_MAX;
            }
        }
        double tmp;
        if(fixflag){
            t1=std::chrono::high_resolution_clock::now();
            tmp = DijkstraQuery(queryset[i].first, queryset[i].second, reg, 1);
            t2=std::chrono::high_resolution_clock::now();
        }
        else{
            t1=std::chrono::high_resolution_clock::now();
            tmp = DijkstraQuery(queryset[i].first, queryset[i].second, rega[i], 0);
            t2=std::chrono::high_resolution_clock::now();
        }
        time_span = std::chrono::duration_cast<std::chrono::duration<double>>(t2-t1);
        runT += time_span.count();
        ans.push_back(tmp);
    }        
    cout << (qi).c_str() << " Query Time " << runT*1000 << endl;
    setres += (qi);
    setres += string(" Query Time \n") + to_string(runT*1000) + string("\n");

    FILE *fp_out = fopen((s3+string("DijkstraResults")).c_str(), "w");
    for (int i = 0; i < ans.size(); i++)
        fprintf(fp_out, "%f\n", ans[i]);
    fclose(fp_out);
}

int main(int argc , char * argv[]){
    string sfile, sq, srandom,sreg;
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
            adjL[u].push_back(edge(u, v, w, l));
            adj[u][v] = DC(w, l);
            adjL[v].push_back(edge(v, u, w, l));
            adj[v][u] = DC(w, l);
            alledges.push_back(edge(u, v, w, l));
        }
    }
    string setres=sfile+string("\n");
    if (argc > 3){
        setres += sreg + string(":\n");
        rep(sq, sfile, setres, sreg, 1);
    }
    else{
        setres += sreg + string(":\n");
        rep(sq, sfile, setres, sreg, 0);
    }

    FILE *fp_record = fopen("DijkstraRecord.txt", "a");
    fprintf(fp_record, "%s\n", setres.c_str());
    fclose(fp_record);
    return 0;
}