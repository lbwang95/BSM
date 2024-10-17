#include<bits/stdc++.h>
#define MAX_NS 200
#define MAX_S 32
#define MAX_LS 32
using namespace std;
typedef set<int> IntSet;
typedef set<char> CharSet;
struct NfaState{			
	int index;				
	char input;//arcvalue				
	int chTrans;
	IntSet epTrans;//setbyEpsilon
};
struct NFA{
	NfaState *head;	
	NfaState *tail;
};
NfaState NfaStates[MAX_NS];
int nfaStateNum;

void add(NfaState *n1, NfaState *n2, char ch){
	n1->input = ch;
	n1->chTrans = n2->index;
}
//epsilon trans
void add(NfaState *n1, NfaState *n2){
	n1->epTrans.insert(n2->index);
}
NFA creatNFA(int sum){
	NFA n;
	n.head = &NfaStates[sum];
	n.tail = &NfaStates[sum + 1];
	return n;
}
void insert(string &s, int n, char ch){
	s += '#';
	for(int i = s.size() - 1; i > n; i--)
	{
		s[i] = s[i - 1];
	}
	s[n] = ch;
}
 
void preprocess(string &s){
	int i = 0 , length = s.size();
	while(i < length){
		if((s[i] >= 'a' && s[i] <= 'z') || (s[i] == '*') || (s[i] == ')')){
			if((s[i + 1] >= 'a' && s[i + 1] <= 'z') || s[i + 1] == '('){
				insert(s, i+1 , '&');
				length ++;
			}
		}
		i++;
	}
} 

int priority(char ch){
	if(ch == '*')
		return 3;
	if(ch == '&')
		return 2;
	if(ch == '|')
		return 1;
	if(ch == '(')
		return 0;
}

string infixToSuffix(string s)
{
	preprocess(s);			
	string str;				
	stack<char> oper;		
	for(int i = 0; i < s.size(); i++)
	{
		if(s[i] >= 'a' && s[i] <= 'z')	
		{
			str += s[i];
		} 
		else							 
		{
			if(s[i] == '(')			
			{
				oper.push(s[i]);
			} 
			else if(s[i] == ')')	
			{
				char ch = oper.top();
				while(ch != '(')		
				{
					str += ch;
					oper.pop();
					ch = oper.top();
				}
				oper.pop();				 
			}
			else					 
			{
				if(!oper.empty())			 
				{
					char ch = oper.top();
					while(priority(ch) >= priority(s[i]))	 
					{
						str +=	ch;
						oper.pop();
						if(oper.empty())	 
						{
							break;
						} 								
						else ch = oper.top();
					} 
					oper.push(s[i]);		 
				}
				else				
				{
					oper.push(s[i]);
				}
			}
		}
	}
	
	while(!oper.empty())
	{
		char ch = oper.top();
		oper.pop();
		str += ch;
	}
	//cout<<"infix："<<s<<endl; 
	//cout<<"sufix："<<str<<endl;
	return str;
} 

NFA strToNfa(string s)
{
	nfaStateNum = 0;
	stack<NFA> NfaStack;		 
	for(int i = 0; i < s.size(); i++)		 
	{
		if(s[i] >= 'a' && s[i] <= 'z')		 
		{
			NFA n = creatNFA(nfaStateNum);		 
			nfaStateNum += 2;					
			add(n.head, n.tail, s[i]);			
			NfaStack.push(n);					
		}
		else if(s[i] == '*')		
		{
			NFA n1 = creatNFA(nfaStateNum);		
			nfaStateNum += 2;					
			NFA n2 = NfaStack.top();			
			NfaStack.pop();
			add(n2.tail, n1.head);				
			add(n2.tail, n1.tail);				
			add(n1.head, n2.head);				
			add(n1.head, n1.tail);				
			NfaStack.push(n1);					
		}
		else if(s[i] == '|')		
		{
			NFA n1, n2;							
			n2 = NfaStack.top();
			NfaStack.pop();
			n1 = NfaStack.top();
			NfaStack.pop();
			NFA n = creatNFA(nfaStateNum);		
			nfaStateNum +=2;					
			add(n.head, n1.head);				
			add(n.head, n2.head);					
			add(n1.tail, n.tail);				
			add(n2.tail, n.tail);				
			NfaStack.push(n);					
		}
		else if(s[i] == '&')		
		{
			NFA n1, n2, n;				
			n2 = NfaStack.top();				
			NfaStack.pop();
			n1 = NfaStack.top();
			NfaStack.pop();
			add(n1.tail, n2.head);				
			n.head = n1.head;					
			n.tail = n2.tail;					
			NfaStack.push(n);					
		}
	}
	return NfaStack.top();		
}

void printNFA(NFA nfa)
{
	cout<<"***************     NFA     ***************"<<endl; 
	cout<<"NFA StateNum: "<<nfaStateNum<<endl;
	cout<<"Initial State"<<nfa.head->index<<" Final States" <<nfa.tail->index<<"。"<<endl<<"Transtion Function："<<endl;
	for(int i = 0; i < nfaStateNum; i++)		
	{
		if(NfaStates[i].input != '#')			
		{
			cout<<NfaStates[i].index<<"-->'"<<NfaStates[i].input<<"'-->"<<NfaStates[i].chTrans<<'\t';
		}
		IntSet::iterator it;					
		for(it = NfaStates[i].epTrans.begin(); it != NfaStates[i].epTrans.end(); it++)
		{
			cout<<NfaStates[i].index<<"-->'"<<' '<<"'-->"<<*it<<'\t';
		}
		cout<<endl;
	}
}

struct Edge			
{
	char input;			
	int Trans;			
};
struct DfaState		
{
	bool isEnd;			
	int index;			
	IntSet closure;		
	int edgeNum;		
	Edge Edges[MAX_LS];		
};
DfaState DfaStates[MAX_NS];		
int dfaStateNum;			
struct DFA			
{
	int startState;				
	set<int> endStates;			
	set<char> terminator;		
	int trans[MAX_NS][26];		
};

IntSet epcloure(IntSet s)
{
	stack<int> epStack;		
	IntSet::iterator it;
	for(it = s.begin(); it != s.end(); it++)
	{
		epStack.push(*it);			
	}
	while(!epStack.empty())			
	{
		int temp = epStack.top();		
		epStack.pop();
		IntSet::iterator iter;
		for(iter = NfaStates[temp].epTrans.begin(); iter != NfaStates[temp].epTrans.end(); iter++)
		{
			if(!s.count(*iter))				
			{								
				s.insert(*iter);			
				epStack.push(*iter);		
			}
		}
	}
	return s;		
}

IntSet moveEpCloure(IntSet s, char ch)
{
	IntSet temp;
	IntSet::iterator it;
	for(it = s.begin(); it != s.end(); it++)		
	{
		if(NfaStates[*it].input == ch)				
		{
			temp.insert(NfaStates[*it].chTrans);		
		}
	}
	temp = epcloure(temp);			
	return temp;
}

bool IsEnd(NFA n, IntSet s)
{
	IntSet::iterator it;
	for(it = s.begin(); it != s.end(); it++)	
	{
		if(*it == n.tail->index)				
		{
			return true;
		}
	}
	return false;		
}

DFA nfaToDfa(NFA n, string str)		
{
	//cout<<"***************     DFA     ***************"<<endl; 
	int i;
	dfaStateNum = 0;
	DFA d;
	set<IntSet> states;		
	memset(d.trans, -1, sizeof(d.trans));	 
	for(i = 0; i < str.size(); i++)			
	{
		if(str[i] >= 'a' && str[i] <= 'z')		
		{
			d.terminator.insert(str[i]);
		}
	}
	d.startState = 0;		
	IntSet tempSet;
	tempSet.insert(n.head->index);		
	DfaStates[0].closure = epcloure(tempSet);		
	DfaStates[0].isEnd = IsEnd(n, DfaStates[0].closure);		
	dfaStateNum++;			
	queue<int> q;
	q.push(d.startState);		
	while(!q.empty())		
	{
		int num = q.front();				
		q.pop();
		CharSet::iterator it;
		for(it = d.terminator.begin(); it != d.terminator.end(); it++)		
		{
			IntSet temp = moveEpCloure(DfaStates[num].closure, *it);		
			/*IntSet::iterator t;
			cout<<endl;
			for(t = temp.begin(); t != temp.end(); t++)
			{
				cout<<*t<<' ';
			}
			cout<<endl;*/
			if(!states.count(temp) && !temp.empty())	
			{
				states.insert(temp);				
				DfaStates[dfaStateNum].closure = temp;
				DfaStates[num].Edges[DfaStates[num].edgeNum].input = *it;				
				DfaStates[num].Edges[DfaStates[num].edgeNum].Trans = dfaStateNum;		
				DfaStates[num].edgeNum++;												
				d.trans[num][*it - 'a'] = dfaStateNum;		
				DfaStates[dfaStateNum].isEnd = IsEnd(n, DfaStates[dfaStateNum].closure);	
				q.push(dfaStateNum);		
				dfaStateNum++;		
			}
			else			
			{
				for(i = 0; i < dfaStateNum; i++)		
				{
					if(temp == DfaStates[i].closure)		
					{
						DfaStates[num].Edges[DfaStates[num].edgeNum].input = *it;		
						DfaStates[num].Edges[DfaStates[num].edgeNum].Trans = i;			
						DfaStates[num].edgeNum++;										
						d.trans[num][*it - 'a'] = i;		
						break;
					}
				}
			}
		}
	}
	
	for(i = 0; i < dfaStateNum; i++)		
	{
		if(DfaStates[i].isEnd == true)		
		{
			d.endStates.insert(i);		
		}
	}
	return d;
}

void printDFA(DFA d)
{
	int i, j;
	cout<<"DFA State Num"<<dfaStateNum<<"Initial State"<<d.startState<<endl;
	cout<<"Alphabet｛ ";
	set<char>::iterator it;
	for(it = d.terminator.begin(); it != d.terminator.end(); it++)
	{
		cout<<*it<<' ';
	}
	cout<<'}'<<endl;
	cout<<"Final States｛ "; 
	IntSet::iterator iter;
	for(iter = d.endStates.begin(); iter != d.endStates.end(); iter++)
	{
		cout<<*iter<<' ';
	}
	cout<<'}'<<endl;
	cout<<"Transition："<<endl;
	for(i = 0; i < dfaStateNum; i++)
	{
		for(j = 0; j < DfaStates[i].edgeNum; j++)
		{
			if(DfaStates[DfaStates[i].Edges[j].Trans].isEnd == true)
			{
				cout<<DfaStates[i].index<<"-->'"<<DfaStates[i].Edges[j].input;
				cout<<"'--><"<<DfaStates[i].Edges[j].Trans<<">\t";
			}
			else
			{
				cout<<DfaStates[i].index<<"-->'"<<DfaStates[i].Edges[j].input;
				cout<<"'-->"<<DfaStates[i].Edges[j].Trans<<'\t';
			}
		}
		cout<<endl;
	}
	cout<<endl<<"TransMatrix："<<endl<<"     ";
	CharSet::iterator t;
	for(t = d.terminator.begin(); t != d.terminator.end(); t++)
	{
		cout<<*t<<"   ";
	}
	cout<<endl;
	for(i = 0; i < dfaStateNum; i++)
	{
		if(d.endStates.count(i))
		{
			cout<<'<'<<i<<">  ";
		}
		else
		{
			cout<<' '<<i<<"   ";
		}
		for(j = 0; j < 26; j++)
		{
			if(d.terminator.count(j + 'a'))
			{
				if(d.trans[i][j] != -1)
				{
					cout<<d.trans[i][j]<<"   ";
				}
				else
				{
					cout<<"    "; 
				}
			}
		}
		cout<<endl;
	}
}

IntSet s[MAX_NS];					
DfaState minDfaStates[MAX_NS];		
int minDfaStateNum;			
struct stateSet			
{
	int index;			  
	IntSet s;			
};

int findSetNum(int count, int n)
{
	for(int i = 0; i < count; i++)
	{
		if(s[i].count(n))
		{						
			return i;
		}
	}
}
bool finalFlag[MAX_NS];
bool terminalFlag[MAX_NS];

DFA minDFA(DFA d)
{
	int i, j;
	minDfaStateNum = 0;
	//cout<<endl<<"*************     minDFA     **************"<<endl;
	DFA minDfa;
	minDfa.terminator = d.terminator;		
	memset(minDfa.trans, -1, sizeof(minDfa.trans));

	bool endFlag = true;					 
	for(i = 0; i < dfaStateNum; i++)	
	{
		if(DfaStates[i].isEnd == false)			
		{
			endFlag = false;						
			minDfaStateNum = 2;						
			s[1].insert(DfaStates[i].index);		
		}
		else									
		{
			s[0].insert(DfaStates[i].index);		
		}
	}
	if(endFlag)					
	{
		minDfaStateNum = 1;			
	}
	bool cutFlag = true;		
	while(cutFlag)				
	{
		int cutCount = 0;			
		for(i = 0; i < minDfaStateNum; i++)			
		{
			CharSet::iterator it;
			for(it = d.terminator.begin(); it != d.terminator.end(); it++)		
			{
				int setNum = 0;				
				stateSet temp[1000];			
				IntSet::iterator iter;
				for(iter = s[i].begin(); iter != s[i].end(); iter++)		
				{
					bool epFlag = true;			
					for(j = 0; j < DfaStates[*iter].edgeNum; j++)		
					{
						if(DfaStates[*iter].Edges[j].input == *it)		
						{
							epFlag = false;			
							
							int transNum = findSetNum(minDfaStateNum, DfaStates[*iter].Edges[j].Trans);
							int curSetNum = 0;			
							while((temp[curSetNum].index != transNum) && (curSetNum < setNum))
							{
								curSetNum++;
							}
							if(curSetNum == setNum)		
							{
								
								temp[setNum].index = transNum;			
								temp[setNum].s.insert(*iter);		
								setNum++;		
							}
							else			
							{
								temp[curSetNum].s.insert(*iter);	
							}
						}
					}
					if(epFlag)		
					{
						int curSetNum = 0;
						while((temp[curSetNum].index != -1) && (curSetNum < setNum))
						{
							curSetNum++;
						}
						if(curSetNum == setNum)			
						{
							
							temp[setNum].index = -1;			
							temp[setNum].s.insert(*iter);		
							setNum++;		
						}
						else			
						{
							temp[curSetNum].s.insert(*iter);	
						}
					}	
				}
				if(setNum > 1)	
				{
					cutCount++;		
					
					for(j = 1; j < setNum; j++)		
					{
						IntSet::iterator t;
						for(t = temp[j].s.begin(); t != temp[j].s.end(); t++)
						{
							s[i].erase(*t);						
							s[minDfaStateNum].insert(*t);		
						}
						minDfaStateNum++;		
					}
				}
			}	
		}
		if(cutCount == 0)		
		{
			cutFlag = false;
		}
	}
	
	for(i = 0; i < minDfaStateNum; i++)
	{
		IntSet::iterator y;
		for(y = s[i].begin(); y != s[i].end(); y++)		
		{
			if(*y == d.startState)			
			{
				minDfa.startState = i;
			}
			if(d.endStates.count(*y))		
			{
				minDfaStates[i].isEnd = true;
				minDfa.endStates.insert(i);		
			}
			for(j = 0; j < DfaStates[*y].edgeNum; j++)		
			{
				
				for(int t = 0; t < minDfaStateNum; t++)
				{
					if(s[t].count(DfaStates[*y].Edges[j].Trans))
					{
						bool haveEdge = false;		
						for(int l = 0; l < minDfaStates[i].edgeNum; l++)	
						{					
							if((minDfaStates[i].Edges[l].input == DfaStates[*y].Edges[j].input) && (minDfaStates[i].Edges[l].Trans == t))
							{
								haveEdge = true;		
							}
						}
						if(!haveEdge)		
						{
							minDfaStates[i].Edges[minDfaStates[i].edgeNum].input = DfaStates[*y].Edges[j].input;	
							minDfaStates[i].Edges[minDfaStates[i].edgeNum].Trans = t;	
							minDfa.trans[i][DfaStates[*y].Edges[j].input - 'a'] = t;	
							minDfaStates[i].edgeNum++;		
						}
						break;
					}
				}
			}
		}
	}
	memset(finalFlag, 0, sizeof(finalFlag));
	memset(terminalFlag, 0, sizeof(terminalFlag));
	IntSet::iterator iter;
	for(iter = minDfa.endStates.begin(); iter != minDfa.endStates.end(); iter++){
		finalFlag[*iter] = true;
	}
	CharSet::iterator iter1;
	for(iter1 = minDfa.terminator.begin(); iter1 != minDfa.terminator.end(); iter1++){
		terminalFlag[(*iter1)-'a'] = true;
	}
	return minDfa;
}
void printMinDFA(DFA d)
{
	int i, j;
	cout<<"minDFA StateNum: "<<minDfaStateNum<<"\nInitial State:"<<d.startState<<endl;
	cout<<"Alphabet:{";
	set<char>::iterator it;
	for(it = d.terminator.begin(); it != d.terminator.end(); it++)
		cout<<*it<<' ';
	cout<<'}'<<endl;
	cout<<"Final States:{"; 
	IntSet::iterator iter;
	for(iter = d.endStates.begin(); iter != d.endStates.end(); iter++)
		cout<<*iter<<' ';
	cout<<'}'<<endl;
	cout<<"Transition Function："<<endl;
	for(i = 0; i < minDfaStateNum; i++){
		for(j = 0; j < minDfaStates[i].edgeNum; j++){
			if(minDfaStates[minDfaStates[i].Edges[j].Trans].isEnd == true){
				cout<<minDfaStates[i].index<<"-->'"<<minDfaStates[i].Edges[j].input;
				cout<<"'--><"<<minDfaStates[i].Edges[j].Trans<<">\t";
			}
			else{
				cout<<minDfaStates[i].index<<"-->'"<<minDfaStates[i].Edges[j].input;
				cout<<"'-->"<<minDfaStates[i].Edges[j].Trans<<'\t';
			}
		}
		cout<<endl;
	}
	cout<<endl<<"TransMatrix："<<endl<<"     ";
	CharSet::iterator t;
	for(t = d.terminator.begin(); t != d.terminator.end(); t++)
		cout<<*t<<"   ";
	cout<<endl;
	for(i = 0; i < minDfaStateNum; i++)
	{
		if(d.endStates.count(i))
			cout<<'<'<<i<<">  ";
		else
			cout<<' '<<i<<"   ";
		for(j = 0; j < 26; j++)
			if(d.terminator.count(j + 'a'))
			{
				if(d.trans[i][j] != -1)
					cout<<d.trans[i][j]<<"   ";
				else
					cout<<"    "; 
			}
		cout<<endl;
	}
}
bool indicator(DFA d, string s){
	int u = d.startState;
	for (int i = 0; i < s.size(); i++){
		u = d.trans[u][s[i]-'a'];
		if (u == -1)
			return false;
	}
	return finalFlag[u];
}

int indicator(DFA d, string s, int u){
	for (int i = 0; i < s.size(); i++){
		u = d.trans[u][s[i]-'a'];
		if (u == -1)
			return -1;
	}
	return u;
}
