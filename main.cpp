//
// Created by chenyuedong on 2024/5/15.
//
#include <iostream>
#include <io.h>
#include <string>
#include <random>
#include <chrono>
#include <unordered_set>
#include <queue>

using namespace std;

const bool debug = true;
const int INT_INF = 0x7f7f7f7f;
const int MAX_M = 1000;
const int MAX_N = 200;
const int CHANNEL_COUNT = 40;
const auto startTime = std::chrono::steady_clock::now();

inline unsigned long long runtime() {
    auto now = std::chrono::steady_clock::now();
    auto duration = std::chrono::duration_cast<std::chrono::milliseconds>(now - startTime);
    return duration.count();
}


struct Edge {
    int from{};
    int to{};
    bool die{};
    int channel[CHANNEL_COUNT + 1]{};//0号不用
    Edge() {
        memset(channel, -1, sizeof(channel));
    }

    void reset() {
        memset(channel, -1, sizeof(channel));
        die = false;//没有断掉
    }
};

struct NearEdge {
    int id;
    int to;
    int weight;
};


struct Business {
    int id{};
    int from{};
    int to{};
    int needChannelLength{};
    int value{};
    bool die{};

    bool operator<(const Business &other) const {
        return value > other.value;
    }

    void reset() {
        die = false;
    }

};


struct Vertex {
    int maxChangeCount{};
    int curChangeCount{};
    unordered_set<int> changeBusIds;
    bool die{};//假设死亡不会变业务,有变通道次数且不die

    void reset() {
        curChangeCount = maxChangeCount;
        changeBusIds.clear();
        die = false;
    }
};

struct Strategy {

    int N{};//节点数

    int M{};//边数
    default_random_engine rad{666};

    vector<Edge> edges;
    vector<Vertex> vertices;
    vector<vector<NearEdge>> graph;//邻接表
    vector<NearEdge> searchGraph[MAX_N + 1];//邻接表
    vector<Business> buses;//邻接表
    struct Point {
        int edgeId;
        int startChannelId;
        int endChannelId;
    };
    vector<vector<Point>> busesOriginResult;//邻接表
    int minDistance[MAX_N + 1][MAX_N + 1]{};//邻接表
    void init() {
        scanf("%d %d", &N, &M);
        edges.resize(M + 1);
        vertices.resize(N + 1);
        for (int i = 1; i <= N; i++) {
            int maxChangeCount;
            scanf("%d", &maxChangeCount);
            vertices[i].curChangeCount = maxChangeCount;
            vertices[i].maxChangeCount = maxChangeCount;
        }
        graph.resize(N + 1);
        for (int i = 1; i <= M; i++) {
            int ui, vi;
            scanf("%d %d", &ui, &vi);
            edges[i].from = ui;
            edges[i].to = vi;
            graph[ui].push_back({i, vi, 1});
        }


        int J;
        scanf("%d", &J);
        buses.resize(J + 1);
        busesOriginResult.resize(J + 1);
        for (int i = 1; i <= J; i++) {
            int Src, Snk, S, L, R, V;
            scanf("%d %d %d %d %d %d", &Src, &Snk, &S, &L, &R, &V);
            buses[i].id = i;
            buses[i].from = Src;
            buses[i].to = Snk;
            buses[i].needChannelLength = R - L + 1;
            buses[i].value = V;
            for (int j = 0; j < S; j++) {
                int edgeId;
                scanf("%d", &edgeId);
                for (int k = L; k <= R; k++) {
                    edges[edgeId].channel[k] = i;
                }
                busesOriginResult[i].push_back({edgeId, L, R});
            }
        }


        queue<int> q;
        for (int i = 1; i <= N; ++i) {
            searchGraph[i] = graph[i];
        }
        for (int start = 1; start <= N; ++start) {
            for (int i = 1; i <= N; ++i) {
                minDistance[start][i] = INT_INF;
            }
            minDistance[start][start] = 0;
            q.push(start);
            int deep = 0;
            while (!q.empty()) {
                int size = int(q.size());
                deep++;
                for (int i = 0; i < size; i++) {
                    int vId = q.front();
                    q.pop();
                    for (const NearEdge &edge: searchGraph[vId]) {
                        if (minDistance[start][edge.to] == INT_INF) {
                            minDistance[start][edge.to] = deep;
                            q.push(edge.to);
                        }
                    }
                }
            }
        }
    }

    void mainLoop() {

    }
};

int main() {
    //        freopen("in.txt", "r", stdin);
//        freopen("out.txt", "w", stdout);
//    SetConsoleOutputCP ( CP_UTF8 ) ;
    static Strategy strategy;
    if (debug) {
        string path = "../data/";
        long long allCost = 0;
        for (int i = 0; i < 10; i++) {
            freopen((path + to_string(i) + "/in.txt").c_str(), "r", stdin);
            freopen((path + to_string(i) + "/out.txt").c_str(), "w", stdout);
            strategy = {};
            strategy.init();
            strategy.mainLoop();
        }
    } else {
        strategy.init();
        strategy.mainLoop();
    }

    return 0;
}
