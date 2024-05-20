//
// Created by chenyuedong on 2024/5/15.
//
#include <iostream>
#include <io.h>
#include <string>
#include <random>
#include <chrono>
#include <unordered_set>
#include <unordered_map>
#include <queue>
#include <cassert>
#include <algorithm>
#include <map>
#include <stack>

using namespace std;

const bool debug = true;
const int INT_INF = 0x7f7f7f7f;
const int MAX_M = 1000;
const int MAX_N = 200;
const int CHANNEL_COUNT = 40;
const auto proStartTime = std::chrono::steady_clock::now();
const int SEARCH_TIME = 89 * 1000;//留1s阈值
inline unsigned long long runtime() {
    auto now = std::chrono::steady_clock::now();
    auto duration = std::chrono::duration_cast<std::chrono::milliseconds>(now - proStartTime);
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
    struct SearchUtils {

        static vector<Point> aStar(int start, int end, int width, vector<NearEdge> searchGraph[MAX_N + 1],
                                   const vector<Edge> &edges, const vector<Vertex> &vertices,
                                   int minDistance[MAX_N + 1][MAX_N + 1]) {
            static int dist[CHANNEL_COUNT + 1][MAX_N + 1]
            , parentEdgeId[CHANNEL_COUNT + 1][MAX_N + 1]
            , parentStartChannel[CHANNEL_COUNT + 1][MAX_N + 1]
            , parentVertexId[CHANNEL_COUNT + 1][MAX_N + 1]
            , timestamp[CHANNEL_COUNT + 1][MAX_N + 1]
            , conflictPoints[CHANNEL_COUNT + 1][MAX_N + 1]
            , timestampId = 1;//距离
            timestampId++;
            struct PointWithChannelDeep {
                int vertexId;
                int startChannel;
                int deep;
            };
            static map<int, stack<PointWithChannelDeep>> cacheMap;
            cacheMap.clear();
            stack<PointWithChannelDeep> tmp;
            for (int i = 1; i <= CHANNEL_COUNT; ++i) {
                dist[i][start] = 0;
                timestamp[i][start] = timestampId;
                parentVertexId[i][start] = -1;//起始点为-1顶点
                tmp.push({start, i, 0});
            }
            cacheMap[minDistance[start][end] * MAX_M] = tmp;
            int endChannel = -1;
            int count = 0;

            while (!cacheMap.empty()) {
                pair<const int, stack<PointWithChannelDeep>> &entry = *cacheMap.begin();
                int totalDeep = entry.first;
                stack<PointWithChannelDeep> sk;
                PointWithChannelDeep poll = sk.top();
                sk.pop();
                if (poll.deep != dist[poll.startChannel][poll.vertexId]) {
                    if (sk.empty()) {
                        cacheMap.erase(totalDeep);
                    }
                    continue;
                }
                if (poll.vertexId == end) {
                    endChannel = poll.startChannel;
                    break;
                }
                int lastChannel = poll.startChannel;
                for (const NearEdge &nearEdge: searchGraph[poll.vertexId]) {
                    int next = nearEdge.to;
                    if (parentVertexId[poll.startChannel][poll.vertexId] == next) {
                        //防止重边
                        continue;
                    }
                    const Edge &edge = edges[nearEdge.id];
                    if (edge.die) {
                        continue;
                    }
                    const int *channel = edge.channel;
                    int freeLength = 0;

                    for (int i = 1; i <= CHANNEL_COUNT; i++) {
                        if (channel[i] == -1) {
                            if (channel[i] == channel[i - 1]) {
                                freeLength++;
                            } else {
                                freeLength = 1;
                            }
                        } else {
                            freeLength = 0;
                        }
                        if (freeLength >= width) {
                            count++;
                            int startChannel = i - width + 1;
                            //用来穷举
                            int nextDistance = poll.deep + nearEdge.weight * MAX_M;
                            if (startChannel != lastChannel) {
                                if (poll.vertexId == start || vertices[poll.vertexId].curChangeCount <= 0) {
                                    //开始节点一定不需要转换,而且也转换不了
                                    continue;
                                }
                                if (vertices[poll.vertexId].die) {
                                    continue;//todo 预测，die之后没法转换,die之后curchangeCount可以直接为0
                                }
                                nextDistance += 1;
                            }

                            if (timestamp[startChannel][next] == timestampId &&
                                dist[startChannel][next] <= nextDistance) {
                                //访问过了，且距离没变得更近
                                continue;
                            }
                            if (conflictPoints[startChannel][next]) {
                                continue;//顶点重复
                            }
                            timestamp[startChannel][next] = timestampId;
                            dist[startChannel][next] = nextDistance;
                            parentStartChannel[startChannel][next] = poll.startChannel;
                            parentEdgeId[startChannel][next] = nearEdge.id;
                            parentVertexId[startChannel][next] = poll.vertexId;
                            PointWithChannelDeep pointWithDeep{next, startChannel, nextDistance};
                            nextDistance += MAX_M * minDistance[next][end];
                            if (!cacheMap.count(nextDistance)) {
                                cacheMap[nextDistance] = {};
                            }
                            cacheMap[nextDistance].push(pointWithDeep);
                        }
                    }
                }
                if (sk.empty()) {
                    cacheMap.erase(totalDeep);
                }
            }
            if (endChannel == -1) {
                return {};
            }
            vector<Point> path;
            int cur = end;
            int curStartChannel = endChannel;
            while (cur != start) {
                int edgeId = parentEdgeId[curStartChannel][cur];
                path.push_back({edgeId, curStartChannel, curStartChannel + width - 1});
                int startChannel = parentStartChannel[curStartChannel][cur];
                cur = parentVertexId[curStartChannel][cur];
                curStartChannel = startChannel;
            }
            reverse(path.begin(), path.end());
            int from = start;
            unordered_set<int> keys;
            keys.insert(from);
            for (Point point: path) {
                Edge edge = edges[point.edgeId];
                int to = edge.from == from ? edge.to : edge.from;
                if (keys.count(to)) {
                    //顶点重复，需要锁死这个通道进入得顶点
                    //return  new ArrayList<>();
                    conflictPoints[point.startChannelId][to] = true;
                    path = aStar(start, end, width, searchGraph, edges, vertices, minDistance);
                    conflictPoints[point.startChannelId][to] = false;
                    return path;
                }
                keys.insert(to);
                from = to;
            }
            return path;
        }
    };


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

    vector<Point> aStarFindPath(Business &business, vector<Point> &originPath) {
        int from = business.from;
        int to = business.to;
        int width = business.needChannelLength;
        undoBusiness(business, originPath, {});

        vector<Point> path = SearchUtils::aStar(from, to, width,
                                                 searchGraph, edges, vertices, minDistance);

        redoBusiness(business, originPath, {});
        return path;
    }

    unordered_set<int> getOriginChangeV(Business &business, const vector<Point> &path) {
        unordered_set<int> originChangeV;
        if (!path.empty()) {
            int from = business.from;
            int lastChannel = path[0].startChannelId;
            for (const Point &point: path) {
                int to = edges[point.edgeId].from == from ?
                         edges[point.edgeId].to
                                                          : edges[point.edgeId].from;
                if (point.startChannelId != lastChannel) {
                    originChangeV.insert(from);
                }
                from = to;
                lastChannel = point.startChannelId;
            }
        }
        return originChangeV;
    }

    void redoBusiness(Business &business, vector<Point> &newPath, const vector<Point> &originPath) {
        unordered_set<int> originChangeV = getOriginChangeV(business, originPath);
        int from = business.from;
        int lastChannel = newPath[0].startChannelId;
        for (const Point &point: newPath) {
            Edge &edge = edges[point.edgeId];
            //占用通道
            for (int j = point.startChannelId; j <= point.endChannelId; j++) {
                edge.channel[j] = business.id;
            }
            int to = edge.from == from ? edge.to : edge.from;
            if (point.startChannelId != lastChannel
                && !originChangeV.count(from)) {//包含可以复用资源
                //变通道，需要减
                vertices[from].curChangeCount--;
                vertices[from].changeBusIds.insert(business.id);
            }
            from = to;
            lastChannel = point.startChannelId;
        }
    }

    unordered_map<int, int> getOriginEdgeIds(const vector<Point> &path) {
        unordered_map<int, int> result;
        if (path.empty()) {
            for (const Point &point: path) {
                result[point.edgeId] = point.startChannelId;
            }
        }
        return result;
    }

    void undoBusiness(Business &business, vector<Point> &newPath, const vector<Point> &originPath) {
        //变通道次数加回来
        unordered_set<int> originChangeV = getOriginChangeV(business, originPath);
        unordered_map<int, int> originEdgeIds = getOriginEdgeIds(originPath);
        int from = business.from;
        int lastChannel = newPath[0].startChannelId;
        for (const Point &point: newPath) {
            Edge &edge = edges[point.edgeId];
            assert(edge.channel[point.startChannelId] == business.id);
            for (int j = point.startChannelId; j <= point.endChannelId; j++) {
                if (originEdgeIds.count(point.edgeId)
                    && j >= originEdgeIds[point.edgeId]
                    && j <= originEdgeIds[point.edgeId]
                            + business.needChannelLength - 1) {
                    continue;
                }
                edge.channel[j] = -1;
            }
            int to = edge.from == from ? edge.to : edge.from;
            if (point.startChannelId != lastChannel && !originChangeV.count(from)) {
                vertices[from].curChangeCount++;
                vertices[from].changeBusIds.erase(business.id);//没改变
                assert(vertices[from].curChangeCount <= vertices[from].maxChangeCount);
            }
            from = to;
            lastChannel = point.startChannelId;
        }
    }

    void printResult(unordered_map<int, vector<Point>> &resultMap) {
        printf("%d\n", int(resultMap.size()));
        for (auto &entry: resultMap) {
            int id = entry.first;
            vector<Point> &newPath = entry.second;
            Business business = buses[id];
            printf("%d %d", business.id, int(newPath.size()));
            for (int j = 0; j < newPath.size(); j++) {
                Point point = newPath[j];
                printf("%d %d %d", point.edgeId, point.startChannelId, point.endChannelId);
                if (j < int(newPath.size()) - 1) {
                    printf(" ");
                } else {
                    printf("\n");
                }
            }
        }
        fflush(stdout);
    }

    void reset() {
        //恢复边和顶点状态
        for (Edge &edge: edges) {
            edge.reset();
        }
        for (Vertex &vertex: vertices) {
            vertex.reset();
        }
        for (Business &bus: buses) {
            bus.reset();
        }
        for (int i = 1; i < busesOriginResult.size(); i++) {
            vector<Point> result = busesOriginResult[i];
            for (const Point &point: result) {
                //只需要占用通道，顶点变换能力不需要，最初没有
                for (int j = point.startChannelId; j <= point.endChannelId; j++) {
                    edges[point.edgeId].channel[j] = i;
                }
            }
        }
        for (int i = 1; i <= N; ++i) {
            searchGraph[i] = graph[i];
        }
    }

    void mainLoop() {
        int t;
        scanf("%d", &t);
        int maxFailLength = 0;
        for (int i = 0; i < t; i++) {
            int curFailLength = 0;

            //邻接表
            vector<vector<Point>> curBusesResult = busesOriginResult;

            while (true) {

                int failEdgeId = -1;
                scanf("%d", &failEdgeId);
                if (failEdgeId == -1) {
                    break;
                }
                assert(failEdgeId != 0);
                //todo 求受影响业务
                edges[failEdgeId].die = true;
                vector<int> affectBusinesses;
                unordered_set<int> ids;
                for (int busId: edges[failEdgeId].channel) {
                    if (busId != -1 && !buses[busId].die) {
                        assert(buses[busId].id == busId);
                        if (!affectBusinesses.empty() && affectBusinesses[affectBusinesses.size() - 1]
                                                         == busId) {
                            continue;
                        }
                        assert(!ids.count(busId));
                        ids.insert(busId);
                        affectBusinesses.push_back(busId);
                    }
                }
                sort(affectBusinesses.begin(), affectBusinesses.end());
                //todo 处理断边
                curFailLength++;
                maxFailLength = max(curFailLength, maxFailLength);
                int iteration = 0;
                int remainTime = int(SEARCH_TIME - runtime());
                int maxSearchTime = remainTime / (t - i) / (max(M / N, maxFailLength));
                maxSearchTime = max(1, maxSearchTime);//至少给个1ms吧，小数据集多次搜索，不浪费
                int startTime = int(runtime());
                vector<int> tmp;
                for (int id: affectBusinesses) {
                    Business &business = buses[id];
                    vector<Point> path = aStarFindPath(business, curBusesResult[business.id]);
                    if (!path.empty()) {
                        tmp.push_back(business.id);
                    } else {
                        business.die = true;//死了没得救
                    }
                }
                affectBusinesses = tmp;
                vector<NearEdge> weightGraph[MAX_N + 1];
                for (int j = 1; j <= N; j++) {
                    weightGraph[j] = searchGraph[j];
                }
                while (runtime() < startTime + maxSearchTime || iteration == 0) {
                    for (int j = 1; j <= N; j++) {
                        shuffle(searchGraph[j].begin(), searchGraph[j].end(), rad);
                    }
                    //todo 按顺序开始搜路径
                    unordered_map<int, vector<Point>> satisfyBusesResult;

                    for (int id: affectBusinesses) {
                        Business &business = buses[id];
                        vector<Point> path = aStarFindPath(business, curBusesResult[business.id]);
                        if (!path.empty()) {
                            satisfyBusesResult[business.id] = path;
                            //变通道次数得减回去
                            redoBusiness(business, path, curBusesResult[business.id]);
                        }
                    }

//                            if (satisfyBusesResult.size() == affectBusinesses.size()) {

                    for (auto &entry: satisfyBusesResult) {
                        int id = entry.first;
                        vector<Point> &newPath = entry.second;
                        Business &business = buses[id];
                        undoBusiness(business, curBusesResult[business.id], newPath);
                        curBusesResult[business.id] = newPath;
                    }
                    printResult(satisfyBusesResult);
                    for (int id: affectBusinesses) {
                        if (!satisfyBusesResult.count(id)) {
                            buses[i].die = true;//死掉了，以后不调度
                        }
                    }
                    break;
//                            }


                    //todo 尝试addBus,两重for，让搜到的undo,搜不到的undo,先搜搜不到的，再搜得到的，如果都能搜到，就赚，此时外层cur保持不变，重新搜


                    //todo 尝试替换bus

                    //todo 保存 恢复源路径重新搜

                    iteration++;
                    //最后随机一下
//                            Collections.shuffle(affectBusinesses, rad);
                }


            }
            reset();


        }
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
