/*
 * Description: SimpleDemo，主要思路是不断随机迭代搜索+选择性拯救业务获得最优解
 * Date: 2024-05-18
 */
#include <iostream>
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
#include <cstring>

using namespace std;

//创建参数
const bool LOCAL_TEST_CREATE = false;//线上改为false
const int CREATE_SAMPLE_RANDOM_SEED = 6;//创建样例种子
const int CREATE_SAMPLE_CANDIDATE_COUNT = 5;//候选序列
const int CREATE_SHUFFLE_CANDIDATE_COUNT = 30;//，每一次随机从20个中选一个
const int CREATE_SHUFFLE_MAX_TRY_COUNT = 5;//不满足相似度约束时，最多尝试几次？
const int CREATE_SAMPLES_MAX_TIME = 74 * 1000;//创建样例最大时间


//创建常量
const int CREATE_SAMPLE_COUNT = 30;//创建样例最大个数
const double CREATE_SAMPLE_SIMILARITY_THRESHOLD = 0.5;//相似度约束
const int EVERY_SCENE_MAX_FAIL_EDGE_COUNT = 60;//一个场景场景最大断边数


//迭代参数
const int SEARCH_RANDOM_SEED = 666;//搜索种子
const int MIN_ITERATION_COUNT = 1;//留1s阈值,他的样例的迭代次数，我们自己的不迭代，防止效果变差
const bool IS_ONLINE = false;//使劲迭代人家的，留1s阈值
const int SMALL_CHANNEL_WEIGHT = 1;//窄通道权重
int CHANGE_CHANNEL_WEIGHT = 1000;//变通道权重
const int EDGE_LENGTH_WEIGHT = 1000;//边的权重


//搜索常量
static int MAX_E_FAIL_COUNT = 4200;//他生成的的样例，最大断边数5k
const int SEARCH_TIME = 90 * 1000;

//其他常量
const int MAX_M = 1000;
const int MAX_N = 200;
const int CHANNEL_COUNT = 40;
const auto programStartTime = std::chrono::steady_clock::now();
const int INT_INF = 0x7f7f7f7f;

inline int runtime() {
    auto now = std::chrono::steady_clock::now();
    auto duration = std::chrono::duration_cast<std::chrono::milliseconds>(now - programStartTime);
    return int(duration.count());
}

inline void printError(const string &s) {
    fprintf(stderr, "%s\n", s.c_str());
    fflush(stderr);
}

//边
struct Edge {
    int from{};
    int to{};
    bool die{};
    int channel[CHANNEL_COUNT + 1]{};//0号不用
    int freeChannelTable[CHANNEL_COUNT + 1][CHANNEL_COUNT + 1]{};//打表加快搜索速度
    bool widthChannelTable[CHANNEL_COUNT + 1][CHANNEL_COUNT + 1]{};//指示某个宽度某条通道是否被占用
    int channelData[CHANNEL_COUNT + 1][3]{};//通道宽度，通道起始点，通道结束点
    Edge() {
        memset(channel, -1, sizeof(channel));
    }

    void reset() {
        memset(channel, -1, sizeof(channel));
        die = false;//没有断掉
    }
};

//邻接表的边
struct NearEdge {
    int id;
    int to;
};

//业务
struct Business {
    int id{};
    int from{};
    int to{};
    int needChannelLength{};
    int value{};
    bool die{};
    int occupyResource{};

    void reset() {
        die = false;
    }

};

//顶点
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

//策略类
struct Strategy {
    int N{};//节点数
    int M{};//边数
    default_random_engine createSampleRad{CREATE_SAMPLE_RANDOM_SEED};
    default_random_engine searchRad{SEARCH_RANDOM_SEED};
    vector<Edge> edges;
    vector<Vertex> vertices;
    vector<vector<NearEdge>> graph;//邻接表
    vector<NearEdge> searchGraph[MAX_N + 1];//邻接表
    vector<NearEdge> baseSearchGraph[MAX_N + 1];//邻接表
    vector<Business> buses;//邻接表
    struct Point {
        int edgeId;
        int startChannelId;
        int endChannelId;
    };
    vector<vector<Point>> busesOriginResult;//邻接表
    int minDistance[MAX_N + 1][MAX_N + 1]{};//邻接表
    unsigned long long searchTime = 0;
    int curHandleCount = 0;
    double maxScore{};
    double curScore{};
    int totalResource = 0;//初始状态剩余的资源
    int totalBusValue = 0;//初始状态剩余的资源
    int remainResource = 0;//初始状态剩余的资源
    int remainAliveBusCount = 0;//初始状态剩余的资源
    int remainAliveBusValue = 0;//初始状态剩余的资源
    int remainEdgesSize = 0;//初始状态剩余的资源
    int createScores[MAX_M + 1]{};//基础分
    vector<vector<int>> baseRepValue[MAX_M + 1];//断掉应该增加的分
    vector<vector<int>> meRepValue[MAX_M + 1];//断掉应该增加的分
    vector<vector<int>> baseOriginValue[MAX_M + 1];//断掉应该增加的分

    struct SearchUtils {
        inline static vector<Point> aStar(int start, int end, int width, const vector<NearEdge> searchGraph[MAX_N + 1],
                                          const vector<Edge> &edges, const vector<Vertex> &vertices,
                                          int minDistance[MAX_N + 1][MAX_N + 1], int maxDeep) {
            struct Common {
                int timestamp;
                int dist;
                int parentChannelVertex;
                int parentEdgeId;
            };
            static Common common[CHANNEL_COUNT + 1][MAX_N + 1];
            static int timestampId = 1;//距离
            static bool conflictPoints[MAX_M + 1][MAX_N + 1];
            static map<int, stack<int>> cacheMap;
            timestampId++;
            cacheMap.clear();
            stack<int> &tmp = cacheMap[minDistance[start][end] * EDGE_LENGTH_WEIGHT * width];
            //往上丢是最好的，因为测试用例都往下丢，往上能流出更多空间
            for (int i = 1; i <= CHANNEL_COUNT; ++i) {
                common[i][start].dist = 0;
                common[i][start].timestamp = timestampId;
                common[i][start].parentChannelVertex = (i << 16) + 0;//起始点为0顶点
                tmp.emplace((i << 16) + start);
            }
            int endChannel = -1;
            while (!cacheMap.empty()) {
                pair<const int, stack<int>> &entry = *cacheMap.begin();
                const int totalDeep = entry.first;
                stack<int> &sk = entry.second;
                const int poll = sk.top();
                sk.pop();
                const int lastChannel = poll >> 16;
                const int lastVertex = poll & 0xFFFF;
                const int lastDeep = common[lastChannel][lastVertex].dist;
                if (lastDeep > maxDeep) {
                    //一定无路可走
                    break;
                }
                if (lastVertex == end) {
                    endChannel = lastChannel;
                    break;
                }
                for (const NearEdge &nearEdge: searchGraph[lastVertex]) {
                    const int next = nearEdge.to;
                    if ((common[lastChannel][lastVertex].parentChannelVertex & 0xFFFF) == next) {
                        //防止重边
                        continue;
                    }
                    const Edge &edge = edges[nearEdge.id];
                    if (edge.die) {
                        continue;
                    }
                    if (conflictPoints[nearEdge.id][next]) {
                        continue;//顶点重复
                    }
                    if (lastVertex == start
                        || vertices[lastVertex].curChangeCount <= 0
                        || vertices[lastVertex].die) {
                        //没法变通道
                        if (!edge.widthChannelTable[width][lastChannel]) {
                            continue;//不空闲直接结束
                        }
                        const int startChannel = lastChannel;
                        int nextDistance = lastDeep + width * EDGE_LENGTH_WEIGHT;//不用变通道
//                        if (edge.channelData[startChannel][0] != width) {
//                            assert (startChannel - edge.channelData[startChannel][1] >= 0);
//                            assert (edge.channelData[startChannel][2] - (startChannel + width) + 1 >= 0);
//                            int lowWidth = startChannel - edge.channelData[startChannel][1];
//                            int heightWidth = edge.channelData[startChannel][2] - (startChannel + width) + 1;
//                            nextDistance +=
//                                    SMALL_CHANNEL_WEIGHT * (min(lowWidth, heightWidth) + lowWidth + heightWidth);
//                        }
                        if (common[startChannel][next].timestamp == timestampId &&
                            common[startChannel][next].dist <= nextDistance) {
                            //访问过了，且距离没变得更近
                            continue;
                        }
                        common[startChannel][next].timestamp = timestampId;
                        common[startChannel][next].dist = nextDistance;
                        common[startChannel][next].parentChannelVertex = (lastChannel << 16) + lastVertex;
                        common[startChannel][next].parentEdgeId = nearEdge.id;
                        cacheMap[nextDistance + width * EDGE_LENGTH_WEIGHT * minDistance[next][end]]
                                .emplace((startChannel << 16) + next);
                    } else {
                        //能变通道
                        const int *freeChannelTable = edge.freeChannelTable[width];
                        for (int i = 1; i <= freeChannelTable[0]; ++i) {
                            const int startChannel = freeChannelTable[i];
                            //用来穷举
                            int nextDistance = lastDeep + width * EDGE_LENGTH_WEIGHT;
//                            if (edge.channelData[startChannel][0] != width) {
//                                assert (startChannel - edge.channelData[startChannel][1] >= 0);
//                                assert (edge.channelData[startChannel][2] - (startChannel + width) + 1 >= 0);
//                                int lowWidth = startChannel - edge.channelData[startChannel][1];
//                                int heightWidth = edge.channelData[startChannel][2] - (startChannel + width) + 1;
//                                nextDistance +=
//                                        SMALL_CHANNEL_WEIGHT * (min(lowWidth, heightWidth) + lowWidth + heightWidth);
//                            }
                            if (startChannel != lastChannel) {
                                nextDistance += CHANGE_CHANNEL_WEIGHT;//变通道距离加1
                            }
                            if (common[startChannel][next].timestamp == timestampId &&
                                common[startChannel][next].dist <= nextDistance) {
                                //访问过了，且距离没变得更近
                                continue;
                            }
                            common[startChannel][next].timestamp = timestampId;
                            common[startChannel][next].dist = nextDistance;
                            common[startChannel][next].parentChannelVertex = (lastChannel << 16) + lastVertex;
                            common[startChannel][next].parentEdgeId = nearEdge.id;
                            cacheMap[nextDistance + width * EDGE_LENGTH_WEIGHT * minDistance[next][end]]
                                    .emplace((startChannel << 16) + next);
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
                int edgeId = common[curStartChannel][cur].parentEdgeId;
                path.push_back({edgeId, curStartChannel, curStartChannel + width - 1});
                int startChannel = common[curStartChannel][cur].parentChannelVertex >> 16;
                cur = common[curStartChannel][cur].parentChannelVertex & 0xFFFF;
                curStartChannel = startChannel;
            }
            reverse(path.begin(), path.end());
            int from = start;
            unordered_set<int> keys;
            keys.insert(from);
            for (const Point &point: path) {
                const Edge &edge = edges[point.edgeId];
                int to = edge.from == from ? edge.to : edge.from;
                if (keys.count(to)) {
                    //顶点重复，锁死这个出边和下一个顶点好一点
                    // return  {};
                    int tmpFrom = start;
                    int lockE = -1;
                    int lockV = -1;
                    for (const Point &point1: path) {
                        const Edge &edge1 = edges[point1.edgeId];
                        if (tmpFrom == to) {
                            lockE = point1.edgeId;
                            lockV = edge1.from == tmpFrom ? edge1.to : edge1.from;
                            break;
                        }
                        tmpFrom = edge1.from == tmpFrom ? edge1.to : edge1.from;
                    }
                    conflictPoints[lockE][lockV] = true;
                    path = aStar(start, end, width, searchGraph, edges, vertices, minDistance, maxDeep);
                    conflictPoints[lockE][lockV] = false;
                    return path;
                }
                keys.insert(to);
                from = to;
            }
            return path;
        }

        //baseLine寻路
        inline static vector<Point>
        baseFind(int start, int end, int width, const vector<NearEdge> searchGraph[MAX_N + 1],
                 const vector<Edge> &edges) {
            struct Common {
                int timestamp;
                int parentEdgeId;
            };
            static Common common[CHANNEL_COUNT + 1][MAX_N + 1];
            static int timestampId = 1;//距离
            timestampId++;
            int endChannel = -1;
            queue<int> q;
            for (int i = 1; i <= CHANNEL_COUNT; ++i) {
                common[i][start].timestamp = timestampId;
                q.emplace((i << 16) + start);
            }
            while (!q.empty()) {
                const int poll = q.front();
                q.pop();
                const int lastChannel = poll >> 16;
                const int lastVertex = poll & 0xFFFF;
                if (lastVertex == end) {
                    endChannel = lastChannel;
                    break;
                }
                for (const NearEdge &nearEdge: searchGraph[lastVertex]) {
                    const int next = nearEdge.to;
                    const Edge &edge = edges[nearEdge.id];
                    if (edge.die) {
                        continue;
                    }

                    //没法变通道
                    if (!edge.widthChannelTable[width][lastChannel]) {
                        continue;//不空闲直接结束
                    }
                    const int startChannel = lastChannel;
                    if (common[startChannel][next].timestamp == timestampId) {
                        //访问过了，且距离没变得更近
                        continue;
                    }
                    common[startChannel][next].timestamp = timestampId;
                    common[startChannel][next].parentEdgeId = nearEdge.id;
                    q.emplace((startChannel << 16) + next);
                }
            }
            if (endChannel == -1) {
                return {};
            }
            vector<Point> path;
            int cur = end;
            int curStartChannel = endChannel;
            while (cur != start) {
                int edgeId = common[endChannel][cur].parentEdgeId;
                path.push_back({edgeId, curStartChannel, curStartChannel + width - 1});
                cur = edges[edgeId].from == cur ? edges[edgeId].to : edges[edgeId].from;
            }
            reverse(path.begin(), path.end());

            return path;
        }

        //baseLine寻路
        inline static vector<Point>
        baseFind2(int start, int end, int width, const vector<NearEdge> searchGraph[MAX_N + 1],
                  const vector<Edge> &edges) {
            struct Common {
                int timestamp;
                int parentEdgeId;
            };
            static Common common[MAX_N + 1];
            static int timestampId = 1;//距离
            int endChannel = -1;
            queue<int> q;
            for (int i = 1; i <= CHANNEL_COUNT; ++i) {
                //按照宽度排序，基本一致
                timestampId++;
                common[start].timestamp = timestampId;
                q.push(start);
                while (!q.empty()) {
                    int size = int(q.size());
                    for (int j = 0; j < size; j++) {
                        int poll = q.front();
                        q.pop();
                        int lastVertex = poll;
                        if (lastVertex == end) {
                            endChannel = i;
                            break;
                        }
                        for (const NearEdge &nearEdge: searchGraph[lastVertex]) {
                            const int next = nearEdge.to;
                            const Edge &edge = edges[nearEdge.id];
                            if (edge.die) {
                                continue;
                            }
                            //没法变通道
                            if (!edge.widthChannelTable[width][i]) {
                                continue;//不空闲直接结束
                            }
                            if (common[next].timestamp == timestampId) {
                                //访问过了，且距离没变得更近
                                continue;
                            }
                            common[next].timestamp = timestampId;
                            common[next].parentEdgeId = nearEdge.id;
                            q.push(next);
                        }
                    }
                    if (endChannel != -1) {
                        break;
                    }
                }
                if (endChannel != -1) {
                    break;
                }
            }

            if (endChannel == -1) {
                return {};
            }
            vector<Point> path;
            int cur = end;
            int curStartChannel = endChannel;
            while (cur != start) {
                int edgeId = common[cur].parentEdgeId;
                path.push_back({edgeId, curStartChannel, curStartChannel + width - 1});
                cur = edges[edgeId].from == cur ? edges[edgeId].to : edges[edgeId].from;
            }
            reverse(path.begin(), path.end());

            return path;
        }

    };

    //恢复场景
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
            vector<Point> &result = busesOriginResult[i];
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
        for (int i = 1; i < edges.size(); i++) {
            Edge &edge = edges[i];
            //计算表
            updateEdgeChannelTable(edge);
        }

        //计算业务占据的资源
        remainResource = totalResource;
        remainAliveBusValue = 0;
        for (int i = 1; i < buses.size(); i++) {
            Business &bus = buses[i];
            bus.occupyResource = calculatesResource(busesOriginResult[bus.id]);
            remainAliveBusValue += bus.value;
            remainResource -= bus.occupyResource;
        }
        remainAliveBusCount = int(buses.size()) - 1;
        remainEdgesSize = int(edges.size()) - 1;
    }

    //获得路径经过的变通道顶点
    inline unordered_set<int> getOriginChangeV(const Business &business, const vector<Point> &path) {
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

    //获得路径经过的边
    inline static unordered_map<int, int> getOriginEdgeIds(const vector<Point> &path) {
        unordered_map<int, int> result;
        if (!path.empty()) {
            for (const Point &point: path) {
                result[point.edgeId] = point.startChannelId;
            }
        }
        return result;
    }

    //更新边的通道表，加快aStar搜索速度使用
    inline static void updateEdgeChannelTable(Edge &edge) {
        const int *channel = edge.channel;
        int (*freeChannelTable)[CHANNEL_COUNT + 1] = edge.freeChannelTable;
        int freeLength = 0;
        memset(edge.widthChannelTable, false, sizeof edge.widthChannelTable);
        memset(edge.channelData, 0, sizeof edge.channelData);
        for (int i = 1; i <= CHANNEL_COUNT; i++) {
            freeChannelTable[i][0] = 0;//长度重新置为0
        }
        static int widthLength[CHANNEL_COUNT + 1];
        memset(widthLength, 0, sizeof widthLength);
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
            if (freeLength > 0) {
                for (int j = freeLength; j > 0; j--) {
                    int start = i - j + 1;
                    widthLength[start] = freeLength;
                    freeChannelTable[j][++freeChannelTable[j][0]] = start;
                    edge.widthChannelTable[j][start] = true;
                    edge.channelData[start][0] = freeLength;
                    edge.channelData[start][1] = i - freeLength + 1;
                    edge.channelData[start][2] = i;
                }
            }
        }
    }

    //在老路径基础上，回收新路径
    inline void undoBusiness(const Business &business, const vector<Point> &newPath, const vector<Point> &originPath) {
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
            updateEdgeChannelTable(edge);
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

    //在老路径基础上，增加新路径
    inline void redoBusiness(const Business &business, const vector<Point> &newPath, const vector<Point> &originPath) {
        unordered_set<int> originChangeV = getOriginChangeV(business, originPath);
        int from = business.from;
        int lastChannel = newPath[0].startChannelId;
        for (const Point &point: newPath) {
            Edge &edge = edges[point.edgeId];
            //占用通道
            for (int j = point.startChannelId; j <= point.endChannelId; j++) {
                assert(edge.channel[j] == -1 || edge.channel[j] == business.id);
                edge.channel[j] = business.id;
            }
            updateEdgeChannelTable(edge);
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

    //aStar寻路
    inline vector<Point>
    aStarFindPath(Business &business, const vector<Point> &originPath, int maxLength, int curLength) {
        int from = business.from;
        int to = business.to;
        int width = business.needChannelLength;
        int l1 = runtime();
        int originResource = calculatesResource(originPath);
        undoBusiness(business, originPath, {});
        double remainBussValues = 1.0 * remainAliveBusValue * max(min(maxLength, int(edges.size()) - 1)
                                                                  - curLength + 1, 1) / (remainEdgesSize + 1);
        //按照价值分资源
        int extraResource = (int) round(0.3 * business.value * remainResource / remainBussValues);
        if (maxLength == curLength) {
            extraResource = INT_INF / 2;
        }
        vector<Point> path = SearchUtils::aStar(from, to, width,
                                                searchGraph, edges, vertices, minDistance,
                                                originResource + extraResource);
        redoBusiness(business, originPath, {});
        int r1 = runtime();
        searchTime += r1 - l1;
        return path;
    }

    // baseLine寻路
    inline vector<Point>
    baseLineFindPath(Business &business) {
        int from = business.from;
        int to = business.to;
        int width = business.needChannelLength;
        int l1 = runtime();
        vector<Point> path = SearchUtils::baseFind(from, to, width, baseSearchGraph, edges);
        int r1 = runtime();
        searchTime += r1 - l1;
        return path;
    }

    //把全部增加上的新路径回收掉
    void undoResult(const unordered_map<int, vector<Point>> &result, const vector<vector<Point>> &curBusesResult,
                    int tmpRemainResource) {
        for (const auto &entry: result) {
            int id = entry.first;
            const vector<Point> &newPath = entry.second;
            Business &business = buses[id];
            const vector<Point> &originPath = curBusesResult[business.id];
            undoBusiness(business, newPath, originPath);
            business.occupyResource = calculatesResource(originPath);
        }
        remainResource = tmpRemainResource;
    }

    //把全部需要增加上的新路径增加进去，并且回收老路径
    void redoResult(vector<int> &affectBusinesses, unordered_map<int, vector<Point>> &result,
                    vector<vector<Point>> &curBusesResult) {
        for (const auto &entry: result) {
            int id = entry.first;
            const vector<Point> &newPath = entry.second;
            const vector<Point> &originPath = curBusesResult[id];
            const Business &business = buses[id];
            //先加入新路径
            redoBusiness(business, newPath, originPath);
            //未错误，误报
            undoBusiness(business, originPath, newPath);
            remainResource += calculatesResource(originPath);
            //断边上的资源无法回收
            remainResource -= business.needChannelLength * EDGE_LENGTH_WEIGHT;
            remainResource -= calculatesResource(newPath);
            curBusesResult[business.id] = newPath;
        }
        for (const int &id: affectBusinesses) {
            Business &business = buses[id];
            if (!result.count(business.id)) {
                business.die = true;//死掉了，以后不调度
                remainAliveBusValue -= business.value;
                remainAliveBusCount -= 1;
            }
        }
    }

    //输出结果
    inline void printResult(const unordered_map<int, vector<Point>> &resultMap) {
        printf("%d\n", int(resultMap.size()));
        for (auto &entry: resultMap) {
            int id = entry.first;
            const vector<Point> &newPath = entry.second;
            Business &business = buses[id];
            printf("%d %d\n", business.id, int(newPath.size()));
            for (int j = 0; j < newPath.size(); j++) {
                const Point &point = newPath[j];
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

    //给路径打分，随机穷举使用
    inline double getEstimateScore(const unordered_map<int, vector<Point>> &satisfyBusesResult) {
        int totalValue = 0;
        for (const auto &entry: satisfyBusesResult) {
            totalValue += buses[entry.first].value;
        }
        //原则，value，width大的尽量短一点
        double plus = 0;
        for (const auto &entry: satisfyBusesResult) {
            int id = entry.first;
            const vector<Point> &newPath = entry.second;
            const Business &business = buses[id];
            int size = int(newPath.size());
            //int width = business.needChannelLength;
            int value = business.value;//价值高，size小好，width暂时不用吧
            plus += 1.0 * value / size;
        }
        return totalValue * 1e9 + plus + 1;
    }


//简单获得一个基础分
    inline unordered_map<int, vector<Point>>
    getBaseLineResult(const vector<int> &affectBusinesses, vector<vector<Point>> &curBusesResult,
                      int maxLength, int curLength, bool base, bool test) {
        unordered_map<int, vector<Point>> satisfyBusesResult;
        for (int id: affectBusinesses) {
            Business &business = buses[id];
            vector<Point> path;
            if (base) {
                path = baseLineFindPath(business);
            } else {
                path = aStarFindPath(business, curBusesResult[business.id], maxLength, curLength);
            }
            if (!path.empty()) {
                //变通道次数得减回去
                redoBusiness(business, path, curBusesResult[business.id]);
                satisfyBusesResult[business.id] = std::move(path);
            }
        }
        return satisfyBusesResult;
    }

    //核心调度函数
    inline void
    dispatch(vector<vector<Point>> &curBusesResult, int failEdgeId, int maxLength, int curLength, bool base,
             bool test, bool shouldPrintf) {
        assert(failEdgeId != 0);
        edges[failEdgeId].die = true;
        if (!test) {
            curHandleCount++;
        }
        remainEdgesSize--;
        for (auto i = searchGraph[edges[failEdgeId].from].begin(); i < searchGraph[edges[failEdgeId].from].end(); ++i) {
            if (i->id == failEdgeId) {
                searchGraph[edges[failEdgeId].from].erase(i);
                break;
            }
        }
        for (auto i = searchGraph[edges[failEdgeId].to].begin(); i < searchGraph[edges[failEdgeId].to].end(); ++i) {
            if (i->id == failEdgeId) {
                searchGraph[edges[failEdgeId].to].erase(i);
                break;
            }
        }
        for (int i = 1; i <= CHANNEL_COUNT; i++) {
            //额外减少的资源
            if (edges[failEdgeId].channel[i] == -1) {
                remainResource -= EDGE_LENGTH_WEIGHT;
            }
        }

        //1.求受影响的业务
        vector<int> affectBusinesses;
        for (int busId: edges[failEdgeId].channel) {
            if (busId != -1 && !buses[busId].die) {
                assert(buses[busId].id == busId);
                if (!affectBusinesses.empty() && affectBusinesses[int(affectBusinesses.size()) - 1]
                                                 == busId) {
                    continue;
                }
                affectBusinesses.push_back(busId);
            }
        }
        sort(affectBusinesses.begin(), affectBusinesses.end(), [&](int aId, int bId) {
            if (base) {

                return buses[aId].value > buses[bId].value;


            } else {
                return buses[aId].occupyResource > buses[bId].occupyResource;
            }
        });
        int affectSize = int(affectBusinesses.size());


        //2.去掉不可能寻到路径的业务，但是因为有重边重顶点，不一定准确，大概准确
//        if (!base && !test) {
//            vector<int> tmp;//还是稍微有点用，减少个数
//            for (int id: affectBusinesses) {
//                Business &business = buses[id];
//                vector<Point> path = aStarFindPath(business, curBusesResult[business.id], maxLength, curLength);
//                if (!path.empty()) {
//                    tmp.push_back(business.id);
//                } else {
//                    business.die = true;//死了没得救
//                }
//            }
//            affectBusinesses = std::move(tmp);
//        }

        //3.循环调度,求出最优解保存
        unordered_map<int, vector<Point>> bestResult;
        double bestScore = -1;
        int remainTime = (int) (SEARCH_TIME - 1000 - int(runtime()));//留1s阈值
        int remainMaxCount = max(1, MAX_E_FAIL_COUNT - curHandleCount + 1);
        int maxRunTime = remainTime / remainMaxCount;
        int tmpRemainResource = remainResource;
        int startTime = runtime();
        int iteration = 0;
        while (((((runtime() - startTime) < maxRunTime) && IS_ONLINE)
                || (iteration < MIN_ITERATION_COUNT)) && (!test || iteration == 0)
                ) {
            if (!test && !base) {
                for (int j = 1; j <= N; j++) {
                    shuffle(searchGraph[j].begin(), searchGraph[j].end(), searchRad);
                }
            }

            unordered_map<int, vector<Point>> satisfyBusesResult = getBaseLineResult(affectBusinesses,
                                                                                     curBusesResult,
                                                                                     maxLength, curLength, base, test
            );


            //2.算分
            double curScore_ = getEstimateScore(satisfyBusesResult);
            if (curScore_ > bestScore) {
                //打分
                bestScore = curScore_;
                bestResult = satisfyBusesResult;
            }

            //3.重排,穷举
            shuffle(affectBusinesses.begin(), affectBusinesses.end(), searchRad);
            undoResult(satisfyBusesResult, curBusesResult, tmpRemainResource);//回收结果，下次迭代
            iteration++;
        }
        redoResult(affectBusinesses, bestResult, curBusesResult);
        if (shouldPrintf) {
            printResult(bestResult);
        }

    }

    static int calculatesResource(const vector<Point> &path) {
        //计算通道资源
        int channelResource = 0;
        int changChannelResource = 0;
        for (int i = 0; i < path.size(); i++) {
            channelResource += EDGE_LENGTH_WEIGHT * (path[i].endChannelId - path[i].startChannelId + 1);
            if (i >= 1 && path[i - 1].startChannelId != path[i].startChannelId) {
                changChannelResource += CHANGE_CHANNEL_WEIGHT;
            }
        }
        return channelResource + changChannelResource;
    }

//初始化
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
            graph[ui].push_back({i, vi});
            graph[vi].push_back({i, ui});
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
                busesOriginResult[i].push_back({edgeId, L, R});
            }
            redoBusiness(buses[i], busesOriginResult[i], {});//防止复赛修改为初始业务也能变通道
        }


        queue<int> q;
        for (int i = 1; i <= N; ++i) {
            searchGraph[i] = graph[i];
            baseSearchGraph[i] = graph[i];
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
        for (int i = 1; i < edges.size(); i++) {
            Edge &edge = edges[i];
            //计算表
            updateEdgeChannelTable(edge);
        }

        int totalChangeCount = 0;
        for (int i = 1; i < vertices.size(); i++) {
            Vertex &vertex = vertices[i];
            totalChangeCount += vertex.maxChangeCount;
        }
        CHANGE_CHANNEL_WEIGHT = EDGE_LENGTH_WEIGHT * (int(edges.size()) - 1) * 2 / totalChangeCount;
        for (int i = 1; i < edges.size(); i++) {
            const Edge &edge = edges[i];
            for (int j = 1; j <= CHANNEL_COUNT; j++) {
                if (edge.channel[j] == -1) {
                    remainResource += EDGE_LENGTH_WEIGHT;
                }
                totalResource += EDGE_LENGTH_WEIGHT;
            }
        }
        for (int i = 1; i < vertices.size(); i++) {
            Vertex &vertex = vertices[i];
            totalResource += CHANGE_CHANNEL_WEIGHT * vertex.maxChangeCount;
            remainResource += CHANGE_CHANNEL_WEIGHT * vertex.curChangeCount;
        }


        //计算业务占据的资源
        for (int i = 1; i < buses.size(); i++) {
            Business &bus = buses[i];
            bus.occupyResource = calculatesResource(busesOriginResult[bus.id]);
            remainAliveBusValue += bus.value;
            totalBusValue += bus.value;
        }
        remainAliveBusCount = int(buses.size());
        remainEdgesSize = int(edges.size()) - 1;

        //剩余的通道数
        int remainChannels = 0;
        for (int i = 1; i < edges.size(); i++) {
            for (int j = 1; j <= CHANNEL_COUNT; j++) {
                if (edges[i].channel[j] == -1) {
                    remainChannels++;
                }
            }
        }
        double failTotalValue =
                1.0 * totalBusValue * min(EVERY_SCENE_MAX_FAIL_EDGE_COUNT, int(edges.size()) - 1) /
                (int(edges.size()) - 1);
        double avgEveryChannelValue = failTotalValue / remainChannels;
        //每个通道变现的价值

        for (int i = 1; i < edges.size(); i++) {
            vector<int> ids = getAllUnDieBusinessId(i);
            edges[i].die = true;
            double baseValue = 0;
            double meValue = 0;
            for (int id: ids) {
                const vector<Point> &originPath = busesOriginResult[id];
                Business &business = buses[id];
                vector<Point> baseFindPath = baseLineFindPath(business);
                vector<Point> meFindPath = aStarFindPath(business, originPath, EVERY_SCENE_MAX_FAIL_EDGE_COUNT, 0);

                if (!baseFindPath.empty()) {
                    baseValue += buses[id].value;
                    baseValue -= (int(baseFindPath.size()) - int(originPath.size())) * business.needChannelLength *
                                 avgEveryChannelValue;
                    for (Point &point: baseFindPath) {
                        vector<int> tmp;
                        tmp.push_back(point.edgeId);
                        tmp.push_back(buses[id].value);
                        baseRepValue[i].push_back(tmp);
                    }
                } else {
                    for (const Point &point: originPath) {
                        vector<int> tmp;
                        tmp.push_back(point.edgeId);
                        tmp.push_back(buses[id].value);
                        baseOriginValue[i].push_back(tmp);
                    }
                }
                if (!meFindPath.empty()) {
                    meValue += buses[id].value;
                    meValue -= (int(meFindPath.size()) - int(originPath.size())) * business.needChannelLength *
                               avgEveryChannelValue;
                    for (Point &point: meFindPath) {
                        vector<int> tmp;
                        tmp.push_back(point.edgeId);
                        tmp.push_back(buses[id].value);
                        meRepValue[i].push_back(tmp);
                    }
                }
            }
            createScores[i] = (int) round(meValue - baseValue);
            edges[i].die = false;
        }

    }

    static bool checkSatisfiedSamplesSimilarity(vector<vector<int>> &samples, vector<int> &curSample) {
        static bool visit[MAX_M + 1];
        for (const vector<int> &sample1: samples) {
            int mergersCount = 0;
            for (const int &item: sample1) {
                visit[item] = true;
                mergersCount++;
            }
            for (const int &item: curSample) {
                if (!visit[item]) {
                    mergersCount++;
                }
            }
            int intersectionCount = 0;
            for (int num: curSample) {
                if (visit[num]) {
                    intersectionCount++;
                }
            }
            for (const int &item: sample1) {
                visit[item] = false;
            }
            if (1.0 * intersectionCount / mergersCount > CREATE_SAMPLE_SIMILARITY_THRESHOLD) {
                return false;
            }
        }
        return true;
    }

    vector<int> getAllUnDieBusinessId(int failEdgeId) {
        vector<int> result;
        Edge &edge = edges[failEdgeId];
        for (int j = 1; j <= CHANNEL_COUNT; j++) {
            if (edge.channel[j] != -1 && edge.channel[j - 1] != edge.channel[j]
                && !buses[edge.channel[j]].die) {
                result.push_back(edge.channel[j]);
            }
        }
        return result;
    }


    vector<int> getBestLengthAndScore(vector<vector<int>> &otherSamples, vector<int> &sample) {
        //最好的长度，以及分差;
        int ourScore[sample.size()];
        int baseScore[sample.size()];

        int curLength = 0;
        int totalValue = 0;
        for (int i = 1; i < buses.size(); ++i) {
            totalValue += buses[i].value;
        }
        for (int i = 0; i < 2; i++) {
            vector<vector<Point>> curBusesResult = busesOriginResult;
            int remainValue = totalValue;
            for (int j = 0; j < sample.size(); j++) {
                int failEdgeId = sample[j];
                vector<int> beforeIds = getAllUnDieBusinessId(failEdgeId);
                dispatch(curBusesResult, failEdgeId, int(sample.size()), curLength, i != 0, true, false);
                for (int beforeId: beforeIds) {
                    if (buses[beforeId].die) {
                        remainValue -= buses[beforeId].value;
                    }
                }
                if (i == 0) {
                    ourScore[j] = remainValue;
                } else {
                    baseScore[j] = remainValue;
                }
            }
            reset();
        }

        //找到分差最大的长度返回
        vector<int> tmp = sample;
        int maxValue = -100000000;
        int bestLength = -1;
        for (int i = int(sample.size()) - 1; i >= 0; i--) {
            int diff = ourScore[i] - baseScore[i];
            if (diff > maxValue && checkSatisfiedSamplesSimilarity(otherSamples, tmp)) {
                maxValue = diff;
                bestLength = i;
            }
            tmp.pop_back();
        }
        vector<int> result;
        result.push_back(bestLength + 1);
        result.push_back(maxValue);
        return result;
    }

    static void printMeCreateSamples(const vector<vector<int>> &curSamples) {
        //输出
        printf("%d\n", int(curSamples.size()));
        for (const vector<int> &curSample: curSamples) {
            printf("%d\n", int(curSample.size()));
            for (int i = 0; i < curSample.size(); i++) {
                printf("%d", curSample[i]);
                if (i < curSample.size() - 1) {
                    printf(" ");
                } else {
                    printf("\n");
                }
            }
        }
        fflush(stdout);
    }

    vector<vector<int>>
    myGenerate(vector<vector<int>> &beforeSample, int initLength, int candidateSize, int returnCount, int type) {
        int saveScores[edges.size()];
        bool beSelect[edges.size()];
        memset(saveScores, 0, sizeof saveScores);
        memset(beSelect, false, sizeof beSelect);

        vector<vector<int>> samples;
        for (int i = 1; i < edges.size(); i++) {
            Edge edge = edges[i];
            int cur = 0;
            for (int j = 1; j <= CHANNEL_COUNT; j++) {
                if (edge.channel[j] != -1 && edge.channel[j - 1] != edge.channel[j]) {
                    if (type == 1) {
                        cur += buses[edge.channel[j]].value;
                    } else if (type == 2) {
                        cur += buses[edge.channel[j]].occupyResource;
                    } else if (type == 3) {
                        cur += buses[edge.channel[j]].needChannelLength;
                    } else if (type == 4) {
                        cur += buses[edge.channel[j]].value;
                    } else if (type == 5) {
                        cur += buses[edge.channel[j]].occupyResource;
                    } else if (type == 6) {
                        cur += buses[edge.channel[j]].needChannelLength;
                    }
                }
            }
            saveScores[i] += cur;
        }
        int scores[edges.size()];
        initLength = min(int(edges.size()) - 1, initLength);
        candidateSize = min(int(edges.size()) - 1, candidateSize);
        struct EdgeIdScore {
            int id;
            int score;
        };
        struct MyBigComparator {
        public:
            bool operator()(const EdgeIdScore &a, const EdgeIdScore &b) const {
                return a.score > b.score;
            }
        };
        struct MyLessComparator {
        public:
            bool operator()(const EdgeIdScore &a, const EdgeIdScore &b) const {
                return a.score < b.score;
            }
        };
        int tryCount = 0;
        while (samples.size() < returnCount) {
            memset(beSelect, false, sizeof beSelect);
            memcpy(scores, saveScores, sizeof scores);
            vector<int> sample;
            for (int i = 0; i < initLength; i++) {
                if (type == 0) {
                    int index = int(createSampleRad() % (int(edges.size()) - 1)) + 1;
                    while (beSelect[index]) {
                        index = int(createSampleRad() % (int(edges.size()) - 1)) + 1;
                    }
                    beSelect[index] = true;
                    sample.push_back(index);
                    continue;
                }
                priority_queue<EdgeIdScore, vector<EdgeIdScore>, MyBigComparator> minScoreQ1;
                priority_queue<EdgeIdScore, vector<EdgeIdScore>, MyLessComparator> maxScoreQ2;
                for (int j = 1; j < edges.size(); j++) {
                    if (beSelect[j]) {
                        continue;
                    }
                    if (type <= 3) {
                        if (minScoreQ1.size() < candidateSize) {
                            minScoreQ1.push({j, scores[j]});
                        }
                        if (scores[j] > minScoreQ1.top().score) {
                            minScoreQ1.pop();
                            minScoreQ1.push({j, scores[j]});
                        }
                    } else {
                        if (maxScoreQ2.size() < candidateSize) {
                            maxScoreQ2.push({j, scores[j]});
                        }
                        if (scores[j] < maxScoreQ2.top().score) {
                            maxScoreQ2.pop();
                            maxScoreQ2.push({j, scores[j]});
                        }
                    }
                }
                //随机选择一个边断掉
                int index = int(createSampleRad() % candidateSize);
                int id = -1;
                for (int j = 0; j <= index; j++) {
                    if (type <= 3) {
                        if (minScoreQ1.empty()) {
                            break;
                        }
                        id = minScoreQ1.top().id;
                        minScoreQ1.pop();
                    } else {
                        if (maxScoreQ2.empty()) {
                            break;
                        }
                        id = maxScoreQ2.top().id;
                        maxScoreQ2.pop();
                    }

                }
                beSelect[id] = true;

                //上面路径上的分数减过去
                vector<int> busIds;
                Edge &edge = edges[id];
                for (int j = 1; j <= CHANNEL_COUNT; j++) {
                    if (edge.channel[j] != -1 && edge.channel[j] != edge.channel[j - 1]) {
                        busIds.push_back(edge.channel[j]);
                    }
                }
                for (int busId: busIds) {
                    const vector<Point> &path = busesOriginResult[busId];
                    for (const Point &point: path) {
                        if (beSelect[point.edgeId]) {
                            continue;
                        }
                        if (type == 1) {
                            scores[point.edgeId] -= buses[busId].value;
                        } else if (type == 2) {
                            scores[point.edgeId] -= buses[busId].occupyResource;
                        } else if (type == 3) {
                            scores[point.edgeId] -= buses[busId].needChannelLength;
                        } else if (type == 4) {
                            scores[point.edgeId] += buses[busId].value;
                        } else if (type == 5) {
                            scores[point.edgeId] += buses[busId].occupyResource;
                        } else if (type == 6) {
                            scores[point.edgeId] += buses[busId].needChannelLength;
                        }
                    }
                }
                sample.push_back(id);
            }
            if (checkSatisfiedSamplesSimilarity(beforeSample, sample)) {
                samples.push_back(sample);
            } else {
                tryCount++;
                if (tryCount > CREATE_SHUFFLE_MAX_TRY_COUNT) {
                    if (initLength == 1) {
                        break;
                    }
                    tryCount = 0;
                    initLength = max(1, (int) (initLength * 0.8));
                }
            }
        }
        return samples;
    }

    vector<vector<int>>
    myGenerate2(vector<vector<int>> &beforeSample, int initLength, int candidateSize, const int returnCount) {
        bool beSelect[edges.size()];
        vector<vector<int>> samples;
        int scores[edges.size()];
        initLength = min(int(edges.size()) - 1, initLength);
        candidateSize = min(int(edges.size()) - 1, candidateSize);
        struct EdgeIdScore {
            int id;
            int score;

            bool operator<(const EdgeIdScore &o1) const {
                return score > o1.score;
            }
        };

        int tryCount = 0;
        while (samples.size() < returnCount) {
            memset(beSelect, false, sizeof beSelect);
            memcpy(scores, createScores, sizeof scores);
            vector<int> sample;
            for (int i = 0; i < initLength; i++) {
                priority_queue<EdgeIdScore> minScoreQ;
                for (int j = 1; j < edges.size(); j++) {
                    if (beSelect[j]) {
                        continue;
                    }
                    if (minScoreQ.size() < candidateSize) {
                        minScoreQ.push({j, scores[j]});
                        continue;
                    }

                    if (scores[j] > minScoreQ.top().score) {
                        minScoreQ.pop();
                        minScoreQ.push({j, scores[j]});
                    }
                }
                //随机选择一个边断掉
                int index = int(createSampleRad() % candidateSize);
                int id = -1;
                for (int j = 0; j <= index; j++) {
                    if (minScoreQ.empty()) {
                        break;
                    }
                    id = minScoreQ.top().id;
                    minScoreQ.pop();
                }
                beSelect[id] = true;

                //上面路径上的分数减过去
                vector<int> busIds;
                Edge &edge = edges[id];
                for (int j = 1; j <= CHANNEL_COUNT; j++) {
                    if (edge.channel[j] != -1 && edge.channel[j] != edge.channel[j - 1]) {
                        busIds.push_back(edge.channel[j]);
                    }
                }
                for (vector<int> &pa: baseRepValue[id]) {
                    //base寻的到的+分，让他死
                    int edId = pa[0];
                    int addScore = pa[1];
                    if (beSelect[edId]) {
                        continue;
                    }
                    scores[edId] += addScore;
                }
                for (vector<int> &pa: baseOriginValue[id]) {
                    //base寻不到的减分，让他活
                    int edId = pa[0];
                    int subScore = pa[1];
                    if (beSelect[edId]) {
                        continue;
                    }
                    scores[edId] -= subScore;
                }
                for (vector<int> &pa: meRepValue[id]) {
                    //自己寻到的让他活
                    int edId = pa[0];
                    int subScore = pa[1];
                    if (beSelect[edId]) {
                        continue;
                    }
                    scores[edId] -= subScore;
                }

                for (int busId: busIds) {
                    const vector<Point> &path = busesOriginResult[busId];
                    for (const Point &point: path) {
                        if (beSelect[point.edgeId]) {
                            continue;
                        }
                        scores[point.edgeId] -= int(round(1.0 * buses[busId].value / int(path.size())));
                    }
                }
                sample.push_back(id);
            }
            if (checkSatisfiedSamplesSimilarity(beforeSample, sample)) {
                samples.push_back(sample);
            } else {
                tryCount++;
                if (tryCount > CREATE_SHUFFLE_MAX_TRY_COUNT) {
                    if (initLength == 1) {
                        break;
                    }
                    tryCount = 0;
                    initLength = max(1, (int) (initLength * 0.8));
                }
            }
        }
        return samples;
    }

//主循环
    void mainLoop() {
        // 生成段
        vector<vector<int>> curSamples;
        vector<int> curSamplesValues;

        //1.选定最好生成策略
        int bestType = 0;
        int maxScore_ = -100000;
//        for (int i = 0; i < 7; i++) {
//            vector<vector<int>> candidateSamples;
//            if (i == 0) {
//                candidateSamples = myGenerate2(curSamples, EVERY_SCENE_MAX_FAIL_EDGE_COUNT,
//                                               CREATE_SHUFFLE_CANDIDATE_COUNT,
//                                               CREATE_SAMPLE_CANDIDATE_COUNT);
//            } else {
//                candidateSamples = myGenerate(curSamples, EVERY_SCENE_MAX_FAIL_EDGE_COUNT,
//                                              CREATE_SHUFFLE_CANDIDATE_COUNT,
//                                              CREATE_SAMPLE_CANDIDATE_COUNT, i);
//            }
//            for (vector<int> &candidateSample: candidateSamples) {
//                vector<int> bestLengthAndScore = getBestLengthAndScore(curSamples, candidateSample);
//                if (bestLengthAndScore[1] > maxScore_) {
//                    maxScore_ = bestLengthAndScore[1];
//                    bestType = i;
//                }
//            }
//        }



        // 2.根据生成策略生成剩余的数据
//        int noBetterCount = 0;
//        int iterateCount = 0;
//        int candidateCount = CREATE_SHUFFLE_CANDIDATE_COUNT;
//        while (true) {
//            iterateCount++;
//            if (curSamples.size() < CREATE_SAMPLE_COUNT) {
//                vector<vector<int>> candidateSamples;
//                if (bestType != 0) {
//                    candidateSamples = myGenerate(curSamples, EVERY_SCENE_MAX_FAIL_EDGE_COUNT,
//                                                  CREATE_SHUFFLE_CANDIDATE_COUNT,
//                                                  CREATE_SAMPLE_CANDIDATE_COUNT, bestType);
//                } else {
//                    candidateSamples = myGenerate2(curSamples, EVERY_SCENE_MAX_FAIL_EDGE_COUNT,
//                                                   CREATE_SHUFFLE_CANDIDATE_COUNT,
//                                                   CREATE_SAMPLE_CANDIDATE_COUNT);
//                }
////                vector<vector<int>> candidateSamples = myGenerate(curSamples, EVERY_SCENE_MAX_FAIL_EDGE_COUNT,
////                                                                  CREATE_SHUFFLE_CANDIDATE_COUNT,
////                                                                  CREATE_SAMPLE_CANDIDATE_COUNT
////                                                                  , 0);
////                vector<vector<int>> candidateSamples = myGenerate2(curSamples, EVERY_SCENE_MAX_FAIL_EDGE_COUNT,
////                                                                   CREATE_SHUFFLE_CANDIDATE_COUNT,
////                                                                   CREATE_SAMPLE_CANDIDATE_COUNT);
//                if (candidateSamples.empty()) {
//                    continue;
//                }
//
//                int bestScore = -100000;
//                vector<int> bestSample;
//                for (vector<int> &candidateSample: candidateSamples) {
//                    vector<int> bestLengthAndScore = getBestLengthAndScore(curSamples, candidateSample);
//                    if (bestLengthAndScore[1] > bestScore) {
//                        bestScore = bestLengthAndScore[1];
//                        bestSample = {candidateSample.begin(), candidateSample.begin() + bestLengthAndScore[0]};
//                    }
//                }
//                curSamples.push_back(bestSample);
//                curSamplesValues.push_back(bestScore);
//            } else {
//                int minIndex = 0;
//                int minValue = curSamplesValues[0];
//                int minSampleLength = int(curSamples[0].size());
//                int maxSampleLength = int(curSamples[0].size());
//                for (int i = 1; i < curSamples.size(); i++) {
//                    if (curSamplesValues[i] < minValue) {
//                        minIndex = i;
//                        minValue = curSamplesValues[i];
//                    }
//                    if (curSamples[i].size() < minSampleLength) {
//                        minSampleLength = int(curSamples[i].size());
//                    }
//
//                    if (int(curSamples[i].size()) > maxSampleLength) {
//                        maxSampleLength = int(curSamples[i].size());
//                    }
//                }
//
//                vector<int> sameIndexes;//相同随机选一个
//                for (int i = 0; i < curSamples.size(); i++) {
//                    if (curSamplesValues[i] == minValue) {
//                        sameIndexes.push_back(i);
//                    }
//                }
//                minIndex = int(createSampleRad() % int(sameIndexes.size()));
//
//                //todo 可以再加1随机
//                int curCreateLength =
//                        minSampleLength + int(createSampleRad() % (maxSampleLength - minSampleLength + 1));
//                vector<vector<int>> tmpSamples;
//                for (int i = 0; i < curSamples.size(); i++) {
//                    if (minIndex != i) {
//                        tmpSamples.push_back(curSamples[i]);
//                    }
//                }
////                vector<vector<int>> candidateSamples = myGenerate(tmpSamples, curCreateLength,
////                                                                  candidateCount, 1
////                                                                  , 0);
////                vector<vector<int>> candidateSamples = myGenerate2(tmpSamples, curCreateLength,
////                                                                   candidateCount, 1);
//                vector<vector<int>> candidateSamples;
//                if (bestType != 0) {
//                    candidateSamples = myGenerate(tmpSamples, curCreateLength,
//                                                  candidateCount, 1, bestType);
//                } else {
//                    candidateSamples = myGenerate2(tmpSamples, curCreateLength,
//                                                   candidateCount, 1);
//                }
//
//                if (candidateSamples.empty()) {
//                    continue;
//                }
//                vector<int> bestLengthAndScore = getBestLengthAndScore(tmpSamples, candidateSamples[0]);
//                if (bestLengthAndScore[1] > minValue) {
//                    curSamples[minIndex] = {candidateSamples[0].begin(),
//                                            candidateSamples[0].begin() + bestLengthAndScore[0]};
//                    curSamplesValues[minIndex] = bestLengthAndScore[1];
//                    noBetterCount = 0;
//                } else {
//                    noBetterCount++;
//                    if (noBetterCount > candidateCount) {
//                        candidateCount = min(int(edges.size()) - 1, candidateCount + 1);
//                        noBetterCount = 0;
//                    }
//                }
//            }
//            long curTime = runtime();
//            if (curTime > CREATE_SAMPLES_MAX_TIME) {
//                break;
//            }
//
//        }
//        int value = 0;
//        for (int curSamplesValue: curSamplesValues) {
//            value += curSamplesValue;
//        }
//
//        printError(
//                "iterateCount:" + to_string(iterateCount) + ",maxValue:" +
//                to_string(totalBusValue * curSamples.size()) +
//                ",value:" + to_string(value));


        printMeCreateSamples(curSamples);
// 规划段 本地测试
        if (LOCAL_TEST_CREATE) {
            double myScore = 0, baseScore = 0;
            for (int i = 0; i < 2; i++) {
                curScore = 0;
                for (auto &curSample: curSamples) {
                    vector<vector<Point>> curBusesResult = busesOriginResult;
                    for (int k = 0; k < curSample.size(); k++) {
                        int failEdgeId = curSample[k];
                        int curLength = k + 1;
                        if (i == 0) {
                            dispatch(curBusesResult, failEdgeId, int(curSample.size()),
                                     curLength, false, true, true);
                        } else {
                            dispatch(curBusesResult, failEdgeId, EVERY_SCENE_MAX_FAIL_EDGE_COUNT,
                                     curLength, true, false, true);
                        }
                    }
                    //邻接表
                    int totalValue = 0;
                    int remainValue = 0;
                    for (int k = 1; k < buses.size(); k++) {
                        totalValue += buses[k].value;
                        if (!buses[k].die) {
                            remainValue += buses[k].value;
                        }
                    }
                    curScore += 10000.0 * remainValue / totalValue;
                    reset();
                }
                if (i == 0) {
                    myScore = curScore;
                } else {
                    baseScore = curScore;
                }
            }
            curScore = (myScore - baseScore);
            printError(
                    "totalScore:" + to_string(curSamples.size() * 10000) + ",myScore:" +
                    to_string(myScore).substr(0, to_string(myScore).length() - 3) +
                    ",baseScore:" + to_string(baseScore).substr(0, to_string(baseScore).length() - 3) +
                    ",diffScore:" +
                    to_string(curScore).substr(0, to_string(curScore).length() - 3));

            return;
        }

        int t;
        scanf("%d", &t);
        maxScore = 10000.0 * t;
        int maxLength = INT_INF;//每一个测试场景的断边数，默认是无穷个，猜测每次都一样
        for (int i = 0; i < t; i++) {
            //邻接表
            vector<vector<Point>> curBusesResult = busesOriginResult;
            int curLength = 0;
            while (true) {
                int failEdgeId = -1;
                scanf("%d", &failEdgeId);
                if (failEdgeId == -1) {
                    break;
                }
                curLength++;
//                if (i < curSamples.size()) {
//                    dispatch(curBusesResult, failEdgeId, int(curSamples[i].size()),
//                             curLength, false, true, true);
//                    //自己的不能迭代，效果会差
//                } else {
                dispatch(curBusesResult, failEdgeId, EVERY_SCENE_MAX_FAIL_EDGE_COUNT,
                         curLength, true, true, true);
                // }
            }
            maxLength = curLength;
            int totalValue = 0;
            int remainValue = 0;
            for (int j = 1; j < buses.size(); j++) {
                totalValue += buses[j].value;
                if (!buses[j].die) {
                    remainValue += buses[j].value;
                }
            }
            curScore += 10000.0 * remainValue / totalValue;
            reset();
        }
    }
};

int main() {
    //    SetConsoleOutputCP ( CP_UTF8 ) ;
//todo 1.估分问题，2.能否不要暴力穷举，加一个不暴力的方式3.重复边或者顶点问题未解决好，4.预测复赛改动点（节点失效or其他？）
    static Strategy strategy;
    if (fopen("../data/0/in.txt", "r") != nullptr) {
        string path = "../data/";
        MAX_E_FAIL_COUNT = 12000;
        for (int i = 0; i < 1; i++) {
            int start = runtime();
            freopen((path + to_string(i) + "/in.txt").c_str(), "r", stdin);
            freopen((path + to_string(i) + "/out.txt").c_str(), "w", stdout);
            strategy = {};
            strategy.init();
            strategy.mainLoop();
            int end = runtime();
            printError("runTime:" + to_string(end - start) + ",aStarTime:" + to_string(strategy.searchTime) +
                       ",maxScore:" +
                       to_string(strategy.maxScore).substr(0, to_string(strategy.maxScore).length() - 3) +
                       ",curScore:" +
                       to_string(strategy.curScore).substr(0, to_string(strategy.curScore).length() - 3));
        }
    } else {
        strategy.init();
        strategy.mainLoop();
    }

    return 0;
}
