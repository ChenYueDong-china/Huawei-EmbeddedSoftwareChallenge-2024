#include <iostream>
#include <vector>
#include <algorithm>
#include <map>
#include <set>
#include <string>
#include <fstream>
#include <unordered_set>

using namespace std;
int v_count, o_e_count, max_sub_dis, port_count;

struct Bus {
	int from, to;
	Bus(int from, int to) :from(from), to(to) {};
};

struct Edge {
	int id, from, to, dis;
	//vector<short> channels;
	short* channels;
	Edge(int from, int to, int dis, int id) :id(id), from(from), to(to), dis(dis) {};
	void initChannel(int P)
	{
		channels = new short[P];
		fill(channels, channels + P, -1);
	};
	bool operator<(const Edge& a1) const {
		if (a1.dis != dis)
		{
			return dis < a1.dis;
		}
		return id < a1.id;
	}
};

struct Result {
	int p_j, m_j, n_j;
	vector<int> crossEdges, crossAmpV;
	Result(int p_j, int m_j, int n_j, vector<int> crossEdges, vector<int> crossAmpV) :
		p_j(p_j), m_j(m_j), n_j(n_j), crossEdges(crossEdges), crossAmpV(crossAmpV) {};
};

map<int, map<int, set<Edge>>> nearTable;

map<int, map<int, set<Edge>>> buildNearTable(vector<Edge> edges) {
	map<int, map<int, set<Edge>>> newTable;
	for (Edge &edge : edges)
	{
		if (edge.to != edge.from)
		{
			newTable[edge.from][edge.to].insert(edge);
			newTable[edge.to][edge.from].insert(edge);
		}
	}
	return newTable;
}

bool input(string path, vector<Edge> &edges, vector<Bus> &buses, vector<Result> &res) {
	//ifstream fin("data.in");
	string path1 = path + "/map.txt";
	string path2 = path + "/businesses.txt";
	string path3 = path + "/result.txt";
	ifstream finmap(path1.c_str());
	if (!finmap.good())
	{
		return false;
	}
	finmap >> v_count >> o_e_count >> port_count >> max_sub_dis;
	for (int i = 0; i < o_e_count; i++)
	{
		int from, to, dis;
		finmap >> from >> to;
		if (from >= v_count || to >= v_count) {
			cout << "���ŷǷ�" << from << "to" << to << endl;
			exit(-1);
		}
		finmap >> dis;
		edges.push_back(Edge(from, to, dis, i));
	}
	finmap.close();

	ifstream finbus(path2.c_str());
	int busCount;
	finbus >> busCount;
	for (int i = 0; i < busCount; i++) {
		int from, to;
		finbus >> from >> to;
		buses.push_back(Bus(from, to));
	}
	finbus.close();

	ifstream finre(path3.c_str());
	int addEdgeCount;
	finre >> addEdgeCount;
	vector<Edge> addEdge;
	for (int i = 0; i < addEdgeCount; i++) {
		int from, to;
		finre >> from >> to;
		if (from >= v_count || to >= v_count) {
			cout << "���ŷǷ�" << from << "to" << to << endl;
			exit(-1);
		}
		addEdge.push_back(Edge(from, to, 0, edges.size()));
	}

	for (int i = 0; i < busCount; i++) {
		int p_j, m_j, n_j;
		finre >> p_j >> m_j >> n_j;
		vector<int> crossEdges;
		int tm;
		for (int j = 0; j < m_j; j++) {
			finre >> tm;
			crossEdges.push_back(tm);
		}
		vector<int> crossAmpV;
		for (int j = 0; j < n_j; j++) {
			finre >> tm;
			crossAmpV.push_back(tm);
		}
		res.push_back(Result(p_j, m_j, n_j, crossEdges, crossAmpV));
	}
	finre.close();

	nearTable = buildNearTable(edges);
	for (Edge &edge : addEdge) {
		if (!nearTable.count(edge.from) || !nearTable[edge.from].count(edge.to) ||
			nearTable[edge.from][edge.to].size() == 0)
		{
			cout << "����˲�����ԭʼ�ߵı�,"
				<< "from:" << edge.from << ",to:" << edge.to << endl;
			exit(-1);
		}
		edge.dis = nearTable[edge.from][edge.to].begin()->dis;
		edges.push_back(edge);
		nearTable[edge.from][edge.to].insert(edge);
		nearTable[edge.to][edge.from].insert(edge);
	}

	return true;
}

long alg(vector<Edge> &edges, vector<Bus> &buses, vector<Result> &res) {
	for (Edge& edge : edges) {
		edge.initChannel(port_count);
	}
	int ampSum = 0;
	int edgeCostSum = 0;
	for (int i = 0; i < res.size(); i++) {
		Result result = res[i];
		edgeCostSum += result.m_j;
		ampSum += result.n_j * 100;

		int curSumDis = 0;
		int curV = buses[i].from;
		int size = edges.size();
		//unordered_set<int> impV;
		for (int &crossEdge : result.crossEdges) {
			if (crossEdge >= size) {
				cout << "�߱�ŷǷ�" << crossEdge;
				exit(-1);
			}
			if (count(result.crossAmpV.begin(), result.crossAmpV.end(), curV)) {
				curSumDis = 0;
			}
			Edge edge = edges[crossEdge];
			int next = -1;
			if (curV == edge.from) {
				next = edge.to;
			}
			else if (curV == edge.to) {
				next = edge.from;
			}
			if (next == -1) {
				cout << "�߲�������ǰ��,"
					<< "curV:" + curV << ",edge.from:" + edge.from << ",edge.to:" + edge.to;
				exit(-1);
			}
			if (edge.channels[result.p_j] != -1) {
				cout << "ͨ���Ѿ������ҵ��ռ��,"
					<< "result.p_j:" + result.p_j << ",edge.id:" + edge.id;
				exit(-1);
			}
			else {
				edge.channels[result.p_j] = (short)i;
			}
			curSumDis += edge.dis;
			if (curSumDis > max_sub_dis) {
				cout << "���ź�δ��ʱ�Ŵ�,"
					<< "curV:" + curV;
				exit(-1);
			}
			curV = next;
		}
		if (curV != buses[i].to) {
			cout << "�ߵ��յ㲻��ҵ���յ�,"
				<< "curV:" + curV << ",bus.to:" + buses[i].to;
			exit(-1);
		}
	}
	return (edges.size() - o_e_count) * 1000000L + ampSum + edgeCostSum;
}

void schedule() {
	string path;
	vector<Edge> edges;
	vector<Bus> buses;
	vector<Result> res;
	long allCost = 0;
	for (int i = 0; i < 2; i++) {
		path = "data/" + to_string(i);
		if (!input(path, edges, buses, res))
		{
			break;
		}
		long calCost = alg(edges, buses, res);
		cout << "i:" + to_string(i) << ",curCost:" + to_string(calCost) << endl;
		allCost += calCost;
		edges.clear();
		buses.clear();
		res.clear();
	}
	cout << "-----------------------------------------\n";
	cout << "allCost:" + to_string(allCost);
	return;
}

int main()
{
//    system("chcp 65001 > nul");
	schedule();
	return 0;
}