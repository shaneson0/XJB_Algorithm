#include "deploy.h"
#include <stdio.h>
#include <string.h>
#include <math.h>
#include <stdlib.h>
#include <algorithm>
#include <vector>
#include <sstream>
#include <iostream>
#include <map>
using namespace std;
const int ESIZE = 20*1000+500*2+1000*2+50;
const int VSIZE = 1000+500+50;
const int INF = 199999999;
const int MXFLOW = 500*5000;
void dw(int &a,int b){ if ((b)< (a)) (a)=(b); }

struct Edge
{
	int from,to,cap,flow,cost;
	Edge(){}
};

struct User
{
	int no;
	int node;
	int flow;
};

struct Item
{
	int flow,cost,node;
	bool operator < (const Item& a) const
	{
		return flow*a.cost > cost*a.flow;
	}
};

Edge edges[ESIZE];
int G[VSIZE][VSIZE];
int newG[VSIZE][VSIZE];
Item best[1000+5];
Edge eg[20*1000+5];
User us[500+5];
int ntou[1000+5];
int h = 0, nc, uc, ec, sc, links;
string str;
char strExt[100000];
double pb[VSIZE];
const char *topo_file = NULL;
vector< map<int,int> > bestKeeper;

struct MCMF
{
	int n,m,s,t;
	int inq[VSIZE];
	int d[VSIZE];
	int p[VSIZE];
	int a[VSIZE];
	int slk[VSIZE];
	int ans;
	int flow;
	int S,T;
	bool vis[VSIZE];
	bool servers[VSIZE];
	void init(int n)
	{
		this->n = n;
		for(int i=0; i<n; i++) G[i][0] = servers[i] = 0;
		m = 0;
		links = 0;
	}

	inline void AddEdge(int from, int to, int cap, int cost)
	{
		Edge &e = edges[m++];
		e.from = from;
		e.to = to;
		e.cap = cap;
		e.flow = 0;
		e.cost = cost;
		G[from][++G[from][0]] = m - 1;
		Edge &e1 = edges[m++];
		e1.from = to;
		e1.to = from;
		e1.cap = 0;
		e1.flow = 0;
		e1.cost = -cost;
		G[to][++G[to][0]] = m - 1;
		//cout<<"insert "<<from<<"->"<<to<<' '<<G[from][0]<<endl;
		//cout<<"insert "<<to<<"->"<<from<<' '<<G[to][0]<<endl;
	}

	int aug(int u,int f, bool print = false)
	{
		int t,left=f;
		if (u == T)
		{
			bestKeeper[u][d[S]] += f;
			ans+=f*d[S];
			flow += f; 
			return f;
		}
		vis[u]=1;
		for (int i = 1; i<=G[u][0]; ++i)
		{
			Edge& e = edges[G[u][i]];
			if (e.flow<e.cap && !vis[e.to])
			{
				t=d[e.to]+e.cost-d[u];
				if (t==0)
				{
					int delt=aug(e.to, e.cap - e.flow < left ? e.cap - e.flow : left,print);
					if (delt>0)
					{
						if(e.to == T)
						{
							servers[u] = 1;
						}
						if(print)
						{
							if(e.flow < 0)
							{
								newG[e.to][e.from] -= delt; 
							}
							else
								newG[e.from][e.to] += delt;
						}
						edges[G[u][i]].flow += delt;
						edges[G[u][i]^1].flow -= delt;

						left-=delt;
					}
					if (left==0) 
						return f;
				}else 
					dw(slk[e.to],t);
			}
		}
		return f-left;
	}

	bool modlabel()
	{
		int delt=INF,i;
		for (i=0;i<n;i++)
			if (!vis[i]) { dw(delt,slk[i]);slk[i]=INF;}
		if (delt==INF) return true;
		for (i=0;i< n;i++)
			if (vis[i]) d[i]+=delt;
		return false;
	}

	inline int MinCost(int s, int t, bool print = false)
	{
		S = s;
		T = t;
		flow = ans=0;
		for (int i=0;i<n;i++) d[i]=0,slk[i]=INF;
		do{
			do {memset(vis,0,sizeof(vis));}while (aug(S,INF, print));
		}while (!modlabel());
		for(int i=0; i<n; ++i)
			ans += servers[i]*sc;
		if(print)cout<<h<<' '<<flow<<' '<<ans << ' '<<S<<' '<<T<<endl;
		if(flow < h)return INF;
		return ans;
	}


	inline int printWay(int u, int p, int a)
	{
		vis[u] = true;
		if(u == n-1)return a;
		for(int i=0; i<n; ++i)
		{
			if(!vis[i] && i != p && newG[u][i] > 0)
			{
				a = (a>newG[u][i])?newG[u][i]:a;
				a = printWay(i, u, a);
				newG[u][i] -= a;
				if(i!=n-1)
				{
					sprintf(strExt, "%d ", i);
					str += strExt;
					//cout<<i<<' ';
				}
				if(u == n-2)
				{
					sprintf(strExt, "%d %d\n", ntou[i], a);
					str += strExt;
					//cout <<ntou[i]<<' '<<a<<'\n';
				}
				return a;
			}
		}
		return INF;
	}
	
	inline void display(int minCost)
	{
		if(minCost >= uc*sc)
		{
			links = uc;
			for(int i=0; i< uc; ++i)
			{
				sprintf(strExt, "%d %d %d\n", us[i].node, us[i].no, us[i].flow);
				str += strExt;
			}
		}
		else
		{
			/*
			for(int i=0;i<nc+2;i++)
			{
				for(int j=0;j<nc+2; j++)
					cout<<newG[i][j]<<' ';
				cout<<endl;
			}
			*/
			links = 0;
			memset(vis, 0, sizeof(vis));
			while(printWay(nc, -1, INF) != INF)
			{
				links++;
				memset(vis, 0, sizeof(vis));
			}
			//printf("%d %d\n", minCost, uc*sc);
		}

		if(links == 0)
			topo_file = "NA";
		else
		{
			sprintf(strExt, "%d\n\n", links);
			str = strExt + str;
			strcpy(strExt, str.c_str());
			strExt[strlen(strExt)-1] = '\0';
			topo_file = strExt;
		}
	}
};

void init(char *s[MAX_EDGE_NUM], int lineNum)
{
	memset(ntou, -1, sizeof(ntou));
	int u,v,c,f;
	sscanf(s[0],"%d%d%d", &nc, &ec, &uc);
	sscanf(s[2],"%d", &sc);
	//printf("%d %d %d\n\r\n%d\n\r\n", nc, ec, uc, sc);
	for(int i=4, j=0; i<4+ec; ++i,++j)
	{
		sscanf(s[i],"%d%d%d%d", &u, &v, &c, &f);
		//printf("%d %d %d %d\n", u, v, c, f);
		eg[j].from = u;
		eg[j].to = v;
		eg[j].cap = c;
		eg[j].cost = f;
	}
	for(int i=4+ec+1, j = 0; i<4+ec+1+uc; ++i, ++j)
	{
		sscanf(s[i],"%d%d%d", &u, &v, &c);
		//printf("%d %d %d\n", u, v, c);
		us[j].no = u;
		us[j].node = v;
		us[j].flow = c;
		h += c;
		ntou[v] = u;
	}
	memset(newG, 0, sizeof(newG));
}

struct Statu
{
	int cost;
	string val;
	Statu():cost(0){val="";}
	Statu(int c, string v):cost(c),val(v){}
	bool operator < (const Statu& sta)
	{
		return val > sta.val;
	}
};

struct GA
{
	static const int POPSZ = 25;
	int no;	
	Statu pop[POPSZ];
	Statu child[POPSZ];
	Statu best;
	int genes;	
	int startgs;
	double possible;
	int startGene[VSIZE];
	MCMF mcmf;

	GA(MCMF& mf):mcmf(mf){}

	void init(int gs, double p)
	{
		genes = gs;
		possible = p;
		no = 0;
		startgs = 0;
		for(int i=0; i<genes; ++i)
			startGene[i] = mcmf.servers[i],startgs += startGene[i];
		int st = 4;	
		if(nc < 200)
			st = 7;	
		else if(nc < 500)
			st = 6;

		//cout<<"start:"<<endl;
		for(int i=0; i<st; ++i)
		{
			int radCnt = 0;
			static char gene[VSIZE];
			for(int j=0; j<genes; ++j)gene[j] = '0';
			for(int j=0; j<genes; ++j)
			{
				if(startGene[j])
					gene[j] = '1';
				else
					++radCnt;	
			}
			if(i == 0)
			{
				gene[genes] = '\0';
				Statu sta(INF, string(gene));
				fitness(sta);
				//cout<<gene<<endl;
				best = sta;
				continue;
			}
			int setCnt = random()%3+1, location = 0;
			for(int j=0; j<setCnt && radCnt > 0; ++j)
			{
				location = random()%radCnt;	
				int zeroCnt = 0;
				for(int k=0; k<genes; ++k)
				{
					if(gene[k] == '0' && zeroCnt++ == location)
					{
						gene[k] = '1';	
					}
				}
				radCnt --;
			}
			gene[genes] = '\0';
			//cout<<gene<<endl;
			Statu sta(INF, string(gene));
			if(canTry(sta.val) && fitness(sta))
			{
				//cout<< sta.cost<<endl;
				if(best.cost > sta.cost)
					best = sta;
				pop[no++] = sta;
			}
		}
		cout<<"pop count: "<< no<<endl;
	}

	inline bool fitness(Statu& sta, bool print = false)
	{
		mcmf.init(nc+2);
		for(int i=0; i<ec; ++i)
		{
			mcmf.AddEdge(eg[i].from, eg[i].to, eg[i].cap, eg[i].cost);
			mcmf.AddEdge(eg[i].to, eg[i].from, eg[i].cap, eg[i].cost);
		}
		for(int i=0; i<uc; ++i)
		{
			mcmf.AddEdge(nc, us[i].node, us[i].flow, 0);
		}
		for(int i=0; i<genes; ++i)
		{
			if(sta.val[i] == '1')
				mcmf.AddEdge(i, nc+1, INF, 0);
		}
		int minCost = INF;
		minCost = mcmf.MinCost(nc, nc+1, print);
		if(print)mcmf.display(minCost);
		if(minCost == INF)return false;
		sta.cost = minCost;
		if(print)cout<<minCost<<endl;
		return true;
	}
	
	inline void selection(int& p1, int& p2)
	{
		do
		{
			p1 = roulettewheel();	
			p2 = roulettewheel();	
		}while(p1 == p2);
	}

	inline int roulettewheel()
	{
		double pm = random()%10000/10000.0;
		double add = 0, total = 0;
		for(int i=0; i<no; ++i)
			total += (2*best.cost - pop[i].cost > 0 ? 2*best.cost - pop[i].cost : 0);
		for(int i=0; i<no; ++i)
		{
			add += (2*best.cost - pop[i].cost > 0 ? 2*best.cost - pop[i].cost : 0);
			if(add/total > pm)
				return i;
		}
		return no - 1;
	}

	inline void update(Statu& sta)
	{
		if(no < POPSZ)
		{
			pop[no++] = sta;
			if(best.cost > sta.cost)
				best = sta;
			return;
		}
		int j = 0, an = 0;
		for(int i = 0; i<no; ++i)
			if(an < pop[i].cost)
				an = pop[i].cost, j = i;
		if(pop[j].cost >= sta.cost)
		{
			pop[j] = sta;
		}
		if(best.cost > sta.cost)
			best = sta;
	}

	inline bool canTry(string& gene)
	{
		for(int i=0; i<no; ++i)
			if(gene == pop[i].val)
				return false;
		int setCnt = 0;
		for(int i=0; i<(int)gene.size(); ++i)
		{
			if(gene[i] == '1')
				++ setCnt;
		}
		if(setCnt < startgs - 2 || setCnt>uc || setCnt == 0)return false;
		return true;
	}

	inline void crossover(int p1, int p2)
	{
		int index = random()%genes;
		string s1 = pop[p1].val;
		string s2 = pop[p2].val;
		string tmp1 = s1.substr(0, index) + s2.substr(index, genes-index);
		string tmp2 = s2.substr(0, index) + s1.substr(index, genes-index);
		Statu po1(INF, tmp1), po2(INF, tmp2);
		if(canTry(po1.val) && fitness(po1))
			update(po1);
		if(canTry(po2.val) && fitness(po2))
			update(po2);
	}

	inline void mutation()
	{
		for(int i=0; i<no; ++i)
		{
			bool flag = false;
			string tmp = pop[i].val;
			for(int j=0; j<genes; ++j)
			{
				double p = random()%1000/1000.0;
				if(p < possible)// && (tmp[j] != best.val[j] || best.val[j] != '1'))
				{
					tmp[j] = (tmp[j] == '0' ? '1':'0');
					flag = true;
				}
			}
			if(flag)
			{
				Statu sta(INF, tmp);
				if(canTry(tmp) && fitness(sta))
				{
					//child[chno++] = sta;
					if(pop[i].cost > sta.cost)
						pop[i] = sta;
					if(best.cost > sta.cost)
						best = sta;
				}
			}
		}
		//for(int i=0; i<chno; ++i)
		//	update(child[i]);
	}

	inline void dispose(int n)
	{
		for(int i=0; i<n; ++i)
		{
			//cout<<"NO: "<<i<<endl;
			//cout<<"people: "<<no<<endl;
			evolution();
		}
	}

	inline void evolution()
	{
		int p1, p2;
		selection(p1, p2);
		crossover(p1, p2);
		mutation();
	}
};

void getBestWays()
{
	MCMF mcmf;	
	
	for(int i=0; i<nc+2; ++i)
	{
		best[i].flow = 0;
		best[i].cost = 1;
		best[i].node = i;
		bestKeeper.push_back(map<int, int>());
		//pb[i] = 0.0;
	}
	for(int i=0; i<nc; ++i)
	{
		mcmf.init(nc+1);
		for(int i=0; i<ec; ++i)
		{
			mcmf.AddEdge(eg[i].from, eg[i].to, eg[i].cap, eg[i].cost);
			mcmf.AddEdge(eg[i].to, eg[i].from, eg[i].cap, eg[i].cost);
		}
		for(int i=0; i<uc; ++i)
		{
			mcmf.AddEdge(nc, us[i].node, us[i].flow, 0);
		}
		mcmf.MinCost(nc, i);
	}

	for(int i=0; i<nc;  ++i)
	{
		int flow = 0, cost = 0;
		for(map<int,int>::iterator it = bestKeeper[i].begin(); it != bestKeeper[i].end(); ++it)
		{
			flow += it->second;
			cost += it->first * it->second;
			if(best[i].flow * (sc+cost) < flow * best[i].cost)		
			{
				//cout<<i<<' '<<it->first<<' '<< it->second<<' '<<flow<<' '<<cost + sc<<endl;
				best[i].flow = flow;
				best[i].cost = cost + sc;
			}	
		}
	}

	sort(best, best+nc);
	/*
	for(int i=0; i<nc; ++i)
	{
		if(best[i].flow > 0)
		{
			pb[best[i].node] = best[i].flow*1.0/best[i].cost;
		}else
			pb[best[i].node] = 0;
	}
	*/
	vector<int> src;
	int sum = 0;
	for(int i=0; i<nc && sum<h; ++i)
	{
	//	printf("%d/%d %d\n", best[i].flow, best[i].cost, best[i].node);
		sum += best[i].flow;
		src.push_back(best[i].node);
	} 
	mcmf.init(nc+2);
	for(int i=0; i<ec; ++i)
	{
		mcmf.AddEdge(eg[i].from, eg[i].to, eg[i].cap, eg[i].cost);
		mcmf.AddEdge(eg[i].to, eg[i].from, eg[i].cap, eg[i].cost);
	}
	for(int i=0; i<uc; ++i)
	{
		mcmf.AddEdge(nc, us[i].node, us[i].flow, 0);
	}
	for(int i=0; i<(int)src.size(); ++i)
	{
		mcmf.AddEdge(src[i], nc+1, INF, 0);
	}
	mcmf.MinCost(nc, nc+1);
	//for(int i=0; i<src.size(); ++i)cout<<src[i]<<' ';
	//cout<<endl;
	for(int i=1;i<G[nc][0]; ++i)
	{
		Edge &e = edges[G[nc][i]];
		if(e.flow < e.cap)
		{
			if(find(src.begin(), src.end(),e.to) == src.end())
			{
				src.push_back(e.to);
			}
		}
	}
	//for(int i=0; i<src.size(); ++i)cout<<src[i]<<' ';
	//cout<<endl;
	mcmf.init(nc+2);
	for(int i=0; i<ec; ++i)
	{
		mcmf.AddEdge(eg[i].from, eg[i].to, eg[i].cap, eg[i].cost);
		mcmf.AddEdge(eg[i].to, eg[i].from, eg[i].cap, eg[i].cost);
	}
	for(int i=0; i<uc; ++i)
	{
		mcmf.AddEdge(nc, us[i].node, us[i].flow, 0);
	}
	for(int i=0; i<(int)src.size(); ++i)
	{
		mcmf.AddEdge(src[i], nc+1, INF, 0);
	}
	int minCost = INF;
	minCost = mcmf.MinCost(nc, nc+1);
	bool ss[VSIZE];
	for(int i=0; i<nc; ++i)
		ss[i] = mcmf.servers[i];
	{
		vector<int> possible;
		possible.clear();
		int second = minCost, possb = 0, k = 0;
		for(int j=0; j<nc; ++j)
		{
			if(mcmf.servers[j] != 0)
				possible.push_back(j);
		}
		for(int j=0; j<(int)possible.size(); ++j)
		{
			possb = possible[j];
			mcmf.init(nc+2);
			for(int i=0; i<ec; ++i)
			{
				mcmf.AddEdge(eg[i].from, eg[i].to, eg[i].cap, eg[i].cost);
				mcmf.AddEdge(eg[i].to, eg[i].from, eg[i].cap, eg[i].cost);
			}
			for(int i=0; i<uc; ++i)
			{
				mcmf.AddEdge(nc, us[i].node, us[i].flow, 0);
			}
			for(int i=0; i<(int)src.size(); ++i)
			{
				if(src[i] != possb && src[i] != -1)
					mcmf.AddEdge(src[i], nc+1, INF, 0);
				if(src[i] == possb)
					k = i;
			}
			int tmp = mcmf.MinCost(nc, nc+1);
			if(tmp < second)
			{
				second = tmp;
				src[k] = -1;
				for(int i=0; i<nc; ++i)
					ss[i] = mcmf.servers[i];
			}
		}
		
	}

	for(int i=0; i<nc; ++i)
		mcmf.servers[i] = ss[i];
	/*
	mcmf.init(nc+2);
	for(int i=0; i<ec; ++i)
	{
		mcmf.AddEdge(eg[i].from, eg[i].to, eg[i].cap, eg[i].cost);
		mcmf.AddEdge(eg[i].to, eg[i].from, eg[i].cap, eg[i].cost);
	}
	for(int i=0; i<uc; ++i)
	{
		mcmf.AddEdge(nc, us[i].node, us[i].flow, 0);
	}
	for(int i=0; i<(int)src.size(); ++i)
	{
		if(src[i] != -1)
			mcmf.AddEdge(src[i], nc+1, INF, 0);
	}
	minCost = mcmf.MinCost(nc, nc+1);
	*/

	GA ga(mcmf);
	ga.init(nc, 0.0012);
	if(nc < 200)
		ga.dispose(18780);
	else if(nc < 500)
		ga.dispose(5580);
	else
		ga.dispose(387);
	ga.fitness(ga.best, true);
	/*
	mcmf.init(nc+2);
	for(int i=0; i<ec; ++i)
	{
		mcmf.AddEdge(eg[i].from, eg[i].to, eg[i].cap, eg[i].cost);
		mcmf.AddEdge(eg[i].to, eg[i].from, eg[i].cap, eg[i].cost);
	}
	for(int i=0; i<uc; ++i)
	{
		mcmf.AddEdge(nc, us[i].node, us[i].flow, 0);
	}
	for(int i=0; i<(int)src.size(); ++i)
	{
		mcmf.AddEdge(src[i], nc+1, INF, 0);
	}
	int minCost = INF;
	minCost = mcmf.MinCost(nc, nc+1, true);
	mcmf.display(minCost);	
	*/
}

//你要完成的功能总入口
void deploy_server(char * topo[MAX_EDGE_NUM], int line_num,char * filename)
{

	// 需要输出的内容
	//char * topo_file = (char *)"17\n\n0 8 0 20\n21 8 0 20\n9 11 1 13\n21 22 2 20\n23 22 2 8\n1 3 3 11\n24 3 3 17\n27 3 3 26\n24 3 3 10\n18 17 4 11\n1 19 5 26\n1 16 6 15\n15 13 7 13\n4 5 8 18\n2 25 9 15\n0 7 10 10\n23 24 11 23";
	init(topo, line_num);
	
	getBestWays();
	// 直接调用输出文件的方法输出到指定文件中(ps请注意格式的正确性，如果有解，第一行只有一个数据；第二行为空；第三行开始才是具体的数据，数据之间用一个空格分隔开)
	
	write_result(topo_file, filename);
}
