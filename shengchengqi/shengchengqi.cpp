#include <iostream>
#include <vector>
#include <algorithm>
#include <map>
#include <set>
#include <string>
#include <fstream>
#include <unordered_set>
#include <unordered_map>
#include <cstdlib>
#include <io.h>
#include <direct.h>

using namespace std;

//var
const int v_count = 5000;
const int b_count = 10000;
const int e_count = 5000;
const int MAX_NEED_PATH_COUNT = 10;
const int last_weight = 10;
const int first_weight = 100;
int max_sub_dis = 1000;
const int port_count = 70;
unordered_map<int, unordered_set<int>> nearTable;
bool *visit;
vector<int> area;

//struct
struct Edge {
	int from, to, dis;
	Edge(int from, int to, int dis) :from(from), to(to), dis(dis) {};
};

struct Bus {
	int from, to, needPathCount;
	Bus(int from, int to,int needPathCount) :from(from), to(to), needPathCount(needPathCount) {};
};

//func
inline int getRandomDis() {
	return rand() % (max_sub_dis - 1) + 1;
}

inline int getRandomV() {
	return rand() % (v_count - 1);
}

void dfs(int cur) {
	if (nearTable.count(cur)) {
		for (int near : nearTable[cur]) {
			if (!visit[near]) {
				visit[near] = true;
				area.push_back(near);
				dfs(near);
			}
		}
	}
}

vector<vector<int>>* getSplitRegion(vector<Edge> *edges) {
	nearTable.clear();

	for (Edge& edge : *edges) {
		nearTable[edge.from].insert(edge.to);
		nearTable[edge.to].insert(edge.from);
	}

	vector<vector<int>>* result = new vector<vector<int>>;
	
	area.clear();
    delete visit;
	visit = new bool[v_count];
    memset(visit,0,sizeof(bool)*v_count);
	for (int i = 0; i < v_count; i++) {
		if (visit[i]) {
			continue;
		}
		visit[i] = true;
		area.clear();
		area.push_back(i);
		dfs(i);
		result->push_back(area);
	}

	return result;
}

vector<Edge>* generateMap(string path){
	//随机生成地图
	//随机生成e_count条边
	vector<Edge> *edges = new vector<Edge>;
	for (int i = 0; i < e_count; i++) {
		edges->push_back(Edge(getRandomV(), getRandomV(), getRandomDis()));
	}
	//写入地图数据
	string path1 = path + "/map.txt";
	ofstream out(path1.c_str());
	//顶点数，边数
	out << to_string(v_count) + " " + to_string(edges->size()) + " " + to_string(port_count) + " " + to_string(max_sub_dis)+"\n";
	for (Edge &edge : *edges) {
		out << to_string(edge.from) + " " + to_string(edge.to) + " " + to_string(edge.dis) + "\n";
	}
	out.close();
	return edges;
}

vector<int> getMyRegion(int cur, vector<vector<int>> avaRegion, vector<int> avaCount) {
	int curSum = 0;
	for (int i = 0; i < avaRegion.size(); i++) {
		curSum += avaCount[i];
		if (cur < curSum) {
			return avaRegion[i];
		}
	}
	return avaRegion[avaRegion.size() - 1];
}

int getRandomNeedPathCount() {
    //1的权重是100，最后一个的权重是50，递减
    int sum = (first_weight + last_weight) * MAX_NEED_PATH_COUNT / 2;
    int curValue =  rand() % (sum - 1) + 1;
    int curSum = 0;
    int start = first_weight;
    double step = (first_weight - last_weight) * 1.0 / MAX_NEED_PATH_COUNT;
    for (int i = 1; i <= MAX_NEED_PATH_COUNT; i++) {
        curSum += start;
        if (curValue <= curSum) {
            return i;
        }
        start -= step;
    }

    return MAX_NEED_PATH_COUNT;
}

void generateBusinesses(string path, vector<vector<int>>* regions){

	//按照区域块的大小，分别在这些区域上生成一些业务
	int regionCount = regions->size();
	int *busCount = new int[regionCount];
	memset(busCount, 0, regionCount * sizeof(int));
	int sum = 0;
	for (int i = 0; i < regionCount; i++) {
		int size = (*regions)[i].size();
		if (size > 1) {
			busCount[i] = size;
			sum += busCount[i];
		}
	}
	for (int i = 0; i < regionCount; i++) {
		busCount[i] = busCount[i] * b_count / sum;
	}
	vector<Bus> buses;
	vector<vector<int>> avaRegion;
	vector<int> avaCount;
	for (int i = 0; i < regions->size(); i++) {
		if (busCount[i] > 0) {
			avaRegion.push_back((*regions)[i]);
			avaCount.push_back(busCount[i]);
		}
	}
    int needPathSum = 0,from,to;
    for (int i = 0; i < b_count; i++) {
        vector<int> curRegion = getMyRegion(i, avaRegion, avaCount);
        if (curRegion.size() == 2)
        {
            from = 0;
            to = 0;
        }
        else {
            from = rand() % (curRegion.size() - 1);
            to = rand() % (curRegion.size() - 2);
        }
        int needPathCount = getRandomNeedPathCount();
        needPathSum += needPathCount;
        if (to >= from) {
            to++;
        }
        buses.push_back(Bus(curRegion[from], curRegion[to], needPathCount));
    }
	string path1 = path + "/businesses.txt";
	ofstream output(path1.c_str());
	//业务数
	output << to_string(buses.size()) + " " + to_string(needPathSum) + "\n";
	for (Bus bus : buses) {
		output << to_string(bus.from) + " " + to_string(bus.to) + " " + to_string(bus.needPathCount) + "\n";
	}
	output.close();
}

void schedule(){
	int No = 0;
	string path;
    system("chcp 65001 > nul");
    char tmp[256];
    getcwd(tmp, 256);
    cout << "当前工作路径: " << tmp << endl;
	for (int i = 0; i < 10; i++) {
		path = "data/" + to_string(i);
		if (access(path.c_str(), 0) != 0) {
			mkdir(path.c_str());
		}
		//生成地图
		vector<Edge> *edges = generateMap(path);
		//判断连通分量
		vector<vector<int>>* splitRegion = getSplitRegion(edges);
		//生成业务
		generateBusinesses(path, splitRegion);
	}
}

int main()
{
    srand(time(NULL));
    schedule();
}