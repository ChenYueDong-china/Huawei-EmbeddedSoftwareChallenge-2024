/*
 * Description: 十分简单的一种解法，主要思路是随机生成穷举最大分差，然后按照剩余资源寻找最短路径
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
#include <bitset>

using namespace std;

//创建参数
const bool LOCAL_TEST_CREATE = true;//线上改为false
const int CREATE_SAMPLE_RANDOM_SEED = 666;//创建样例种子
const int CREATE_BASE_SAMPLE_CANDIDATE_COUNT = 5;//候选序列
const int CREATE_OPTIMIZE_SAMPLE_CANDIDATE_COUNT = 5;//候选序列
const int CREATE_BASE_EDGE_CANDIDATE_COUNT = 15;//大于0号策略时，每一次随机从20个中选一个
const int CREATE_OPTIMIZE_EDGE_CANDIDATE_COUNT = 20;//大于0号策略时，每一次随机从20个中选一个
const int CREATE_SHUFFLE_MAX_TRY_COUNT = 5;//不满足相似度约束时，最多尝试几次？
const int CREATE_BASE_SAMPLES_MAX_TIME = 50 * 1000;//留1s阈值
const int CREATE_OPTIMIZE_SAMPLES_MAX_TIME = CREATE_BASE_SAMPLES_MAX_TIME + 20 * 1000;//留1s阈值


const double MY_SAMPLE_SEARCH_RESOURCE_FACTOR = 1.2;
const double OTHER_SAMPLE_SEARCH_RESOURCE_FACTOR = 1.0;


//创建常量
const int CREATE_SAMPLE_COUNT = 30;//创建样例最大个数
const double CREATE_SAMPLE_SIMILARITY_THRESHOLD = 0.5;//相似度约束
const int EVERY_SCENE_MAX_FAIL_EDGE_COUNT = 60;//一个场景场景最大断边数


//迭代参数
const int SEARCH_RANDOM_SEED = 666;//搜索种子
static bool IS_ONLINE = false;//使劲迭代人家的，留1s阈值
int CHANGE_CHANNEL_WEIGHT = 300;//变通道权重
const int EDGE_LENGTH_WEIGHT = 100;//边的权重


//搜索常量
static int MAX_E_FAIL_COUNT = 4200;//他生成的的样例，最大断边数5k
const int SEARCH_TIME = 90 * 1000;

//其他常量
const int MAX_M = 1000;
const int MAX_N = 200;
const int CHANNEL_COUNT = 40;
const auto programStartTime = std::chrono::steady_clock::now();
const int INT_INF = 0x7f7f7f7f;

int time9 = 0;

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
    bitset<(CHANNEL_COUNT + 1) * (CHANNEL_COUNT + 1)> widthChannelTable;//指示某个宽度某条通道是否被占用
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
    int searchTime = 0;
    int curHandleCount = 0;
    double resultScore[2]{};
    int totalResource = 0;//初始状态剩余的资源
    int remainResource = 0;//初始状态剩余的资源
    double avgEdgeAffectValue = 0;//平均断一条边影响的价值
    int createScores[MAX_M + 1]{};//基础分
    vector<vector<int>> baseRepValue[MAX_M + 1];//断掉应该增加的分
    vector<vector<int>> meRepValue[MAX_M + 1];//断掉应该增加的分
    vector<vector<int>> baseOriginValue[MAX_M + 1];//断掉应该增加的分

    struct SearchUtils {

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
                    if (!edge.widthChannelTable[width * (CHANNEL_COUNT + 1) + lastChannel]) {
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




        inline static vector<Point> aStar2(const int start, const int end, const int width,
                                           const vector<NearEdge> searchGraph[MAX_N + 1],
                                           const vector<Edge> &edges, const vector<Vertex> &vertices,
                                           const int minDistance[MAX_N + 1][MAX_N + 1], const int maxResource) {
            static bitset<MAX_N + 1> parentVertexes[MAX_N + 1][CHANNEL_COUNT + 1];
            struct FastQueue {
                int size = 0;
                int dataDist[CHANNEL_COUNT * MAX_N * 10]{};
                int dataChannelVertex[CHANNEL_COUNT * MAX_N * 10]{};

                void push(int dist, int channelVertex) {
                    //上推
                    int index = size + 1;
                    while (index != 1) {
                        int last = index >> 1;
                        if (dataDist[last] > dist) {
                            //下推；
                            dataDist[index] = dataDist[last];
                            dataChannelVertex[index] = dataChannelVertex[last];
                            index >>= 1;
                        } else {
                            break;
                        }
                    }
                    dataDist[index] = dist;
                    dataChannelVertex[index] = channelVertex;
                    ++size;
                }

                int pop() {
                    //弹出第一个
                    int result = dataChannelVertex[1];
                    //最后一个放入第一个当中，下推
                    int curDist = dataDist[size];
                    int curChannelVertex = dataChannelVertex[size];
                    int index = 1;
                    while (true) {
                        int next = index << 1;
                        if (next > size) break;
                        int curMinDist = dataDist[next];
                        int curMin = next;
                        if (next + 1 <= size && dataDist[next + 1] < curMinDist) {
                            curMinDist = dataDist[next + 1];
                            curMin = next + 1;
                        }
                        if (curMinDist < curDist) {
                            dataDist[index] = dataDist[curMin];
                            dataChannelVertex[index] = dataChannelVertex[curMin];
                            index = curMin;
                        } else {
                            break;
                        }
                    }
                    dataDist[index] = curDist;
                    dataChannelVertex[index] = curChannelVertex;
                    --size;
                    return result;
                }

                bool empty() const {
                    return size == 0;
                }

                void clear() {
                    size = 0;
                }
            };
            static int timestamp[MAX_N + 1][CHANNEL_COUNT + 1], dist[MAX_N + 1][CHANNEL_COUNT + 1]
            , parentStartChannelEdgeId[MAX_N + 1][CHANNEL_COUNT + 1];
            static int timestampId = 1;//距离
            static FastQueue q;
            q.clear();
            timestampId++;
            //往上丢是最好的，因为测试用例都往下丢，往上能流出更多空间
            for (int i = 1; i <= CHANNEL_COUNT; ++i) {
                dist[start][i] = 0;
                timestamp[start][i] = timestampId;
                parentVertexes[start][i].reset();
                q.push(minDistance[start][end] * EDGE_LENGTH_WEIGHT * width, (i << 16) + start);
            }
            int endChannel = -1;
            while (!q.empty()) {
                const int poll = q.pop();
                const int lastChannel = poll >> 16;
                const int lastVertex = poll & 0xFFFF;
                const int lastDeep = dist[lastVertex][lastChannel];
                if (lastVertex == end) {
                    endChannel = lastChannel;
                    break;
                }
                for (const NearEdge &nearEdge: searchGraph[lastVertex]) {
                    const int next = nearEdge.to;
                    if (parentVertexes[lastVertex][lastChannel].test(next)) {
                        //防止重边
                        continue;
                    }
                    const Edge &edge = edges[nearEdge.id];
                    if (edge.die) {
                        continue;
                    }
                    if (lastVertex == start
                        || vertices[lastVertex].curChangeCount <= 0
                        || vertices[lastVertex].die) {
                        //没法变通道
                        if (!edge.widthChannelTable[width * (CHANNEL_COUNT + 1) + lastChannel]) {
                            continue;//不空闲直接结束
                        }
                        const int startChannel = lastChannel;
                        int nextDistance = lastDeep + width * EDGE_LENGTH_WEIGHT;//不用变通道
                        if (timestamp[next][startChannel] == timestampId &&
                            dist[next][startChannel] <= nextDistance) {
                            //访问过了，且距离没变得更近
                            continue;
                        }
                        if (nextDistance + width * EDGE_LENGTH_WEIGHT * minDistance[next][end] > maxResource) {
                            continue;
                        }
                        timestamp[next][startChannel] = timestampId;
                        dist[next][startChannel] = nextDistance;
                        parentStartChannelEdgeId[next][startChannel] = (lastChannel << 16) + nearEdge.id;
                        parentVertexes[next][startChannel] = parentVertexes[lastVertex][lastChannel];
                        parentVertexes[next][startChannel].set(lastVertex);
                        q.push(nextDistance + width * EDGE_LENGTH_WEIGHT * minDistance[next][end],
                               (startChannel << 16) + next);
                    } else {
                        //能变通道
                        const int *freeChannelTable = edge.freeChannelTable[width];
                        for (int i = 1; i <= freeChannelTable[0]; ++i) {
                            const int startChannel = freeChannelTable[i];
                            //用来穷举
                            int nextDistance = lastDeep + width * EDGE_LENGTH_WEIGHT;
                            if (startChannel != lastChannel) {
                                nextDistance += CHANGE_CHANNEL_WEIGHT;//变通道距离加1
                            }
                            if (timestamp[next][startChannel] == timestampId &&
                                dist[next][startChannel] <= nextDistance) {
                                //访问过了，且距离没变得更近
                                continue;
                            }
                            if (nextDistance + width * EDGE_LENGTH_WEIGHT * minDistance[next][end] > maxResource) {
                                continue;
                            }
                            timestamp[next][startChannel] = timestampId;
                            dist[next][startChannel] = nextDistance;
                            parentStartChannelEdgeId[next][startChannel] = (lastChannel << 16) + nearEdge.id;
                            parentVertexes[next][startChannel] = parentVertexes[lastVertex][lastChannel];
                            parentVertexes[next][startChannel].set(lastVertex);
                            q.push(nextDistance + width * EDGE_LENGTH_WEIGHT * minDistance[next][end],
                                   (startChannel << 16) + next);
                        }
                    }
                }
            }
            if (endChannel == -1) {
                return {};
            }
            vector<Point> path;
            int cur = end;
            int curStartChannel = endChannel;
            while (cur != start) {
                int edgeId = (parentStartChannelEdgeId[cur][curStartChannel] & 0xFFFF);
                path.push_back({edgeId, curStartChannel, curStartChannel + width - 1});
                int startChannel = (parentStartChannelEdgeId[cur][curStartChannel] >> 16);
                cur = edges[edgeId].from == cur ? edges[edgeId].to : edges[edgeId].from;
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
                    return {};
                }
                keys.insert(to);
                from = to;
            }
            return path;
        }
    };

    //恢复场景
    void reset() {
        //恢复边和顶点状态
        for (int i = 1; i < edges.size(); i++) {
            edges[i].reset();
        }
        for (int i = 1; i < vertices.size(); i++) {
            vertices[i].reset();
        }
        for (int i = 1; i < buses.size(); i++) {
            buses[i].reset();
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
        for (int i = 1; i < buses.size(); i++) {
            Business &bus = buses[i];
            remainResource -= calculatesResource(busesOriginResult[bus.id]);
        }
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
        int l1 = runtime();
        edge.widthChannelTable.reset();
        for (int i = 1; i <= CHANNEL_COUNT; ++i) {
            freeChannelTable[i][0] = 0;//长度重新置为0
        }
        int freeLength = 0;
        for (int i = 1; i <= CHANNEL_COUNT; ++i) {
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
                for (int j = freeLength; j > 0; --j) {
                    const int start = i - j + 1;
                    freeChannelTable[j][++freeChannelTable[j][0]] = start;
                    edge.widthChannelTable.set(j * (CHANNEL_COUNT + 1) + start);
                }
            }
        }
        int r1 = runtime();
        time9 += r1 - l1;
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
            bool changeChannel = false;
            for (int j = point.startChannelId; j <= point.endChannelId; j++) {
                if (originEdgeIds.count(point.edgeId)
                    && j >= originEdgeIds[point.edgeId]
                    && j <= originEdgeIds[point.edgeId]
                            + business.needChannelLength - 1) {
                    continue;
                }
                changeChannel = true;
                edge.channel[j] = -1;
            }
            if (changeChannel && !edge.die) {
                updateEdgeChannelTable(edge);
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

    //在老路径基础上，增加新路径
    inline void redoBusiness(const Business &business, const vector<Point> &newPath, const vector<Point> &originPath) {
        unordered_set<int> originChangeV = getOriginChangeV(business, originPath);
        int from = business.from;
        int lastChannel = newPath[0].startChannelId;
        for (const Point &point: newPath) {
            Edge &edge = edges[point.edgeId];
            //占用通道
            bool allReuse = true;//全部复用老路径不更新这条边，加快速度
            for (int j = point.startChannelId; j <= point.endChannelId; j++) {
                assert(edge.channel[j] == -1 || edge.channel[j] == business.id);
                if (edge.channel[j] == -1) {
                    allReuse = false;
                    edge.channel[j] = business.id;
                }
                //复用啥都不干
            }
            if (!allReuse && !edge.die) {
                updateEdgeChannelTable(edge);
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

    //aStar寻路
    inline vector<Point>
    aStarFindPath(Business &business, const vector<Point> &originPath, int maxLength, int curLength, bool test) {
        int from = business.from;
        int to = business.to;
        int width = business.needChannelLength;

        int originResource = calculatesResource(originPath);
        undoBusiness(business, originPath, {});


        //方式1,求出剩余需要救的价值
        double remainNeedHelpValue = avgEdgeAffectValue * max(min(maxLength, int(edges.size()) - 1) - curLength + 1, 1);
        double factor = test ? MY_SAMPLE_SEARCH_RESOURCE_FACTOR : OTHER_SAMPLE_SEARCH_RESOURCE_FACTOR;
        int extraResource = (int) round(factor * (1.0 * business.value / remainNeedHelpValue) * remainResource);
        if (maxLength == curLength) {
            extraResource = INT_INF / 2;
        }

        //方式2
        //int extraResource = (int) round(max(EDGE_LENGTH_WEIGHT * business.needChannelLength * 6.0, originResource * 1.6));


        int l1 = runtime();
        vector<Point> path = SearchUtils::aStar(from, to, width,
                                                 searchGraph, edges, vertices, minDistance,
                                                 originResource + extraResource);
        int r1 = runtime();
        searchTime += r1 - l1;
        redoBusiness(business, originPath, {});

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
                    int tmpRemainResource, bool onlyOne) {
        for (const auto &entry: result) {
            int id = entry.first;
            const vector<Point> &newPath = entry.second;
            Business &business = buses[id];
            const vector<Point> &originPath = curBusesResult[business.id];
            if (!onlyOne) {
                undoBusiness(business, newPath, originPath);
            }
        }
        remainResource = tmpRemainResource;
    }

    //把全部需要增加上的新路径增加进去，并且回收老路径
    void redoResult(vector<int> &affectBusinesses, unordered_map<int, vector<Point>> &result,
                    vector<vector<Point>> &curBusesResult, bool onlyOne) {
        for (const auto &entry: result) {
            int id = entry.first;
            const vector<Point> &newPath = entry.second;
            const vector<Point> &originPath = curBusesResult[id];
            const Business &business = buses[id];
            //先加入新路径
            if (!onlyOne) {
                redoBusiness(business, newPath, originPath);
            }
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
                path = aStarFindPath(business, curBusesResult[business.id], maxLength, curLength, test);
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

        if (base) {
            sort(affectBusinesses.begin(), affectBusinesses.end(), [&](int aId, int bId) {
                return aId < bId;
            });
            sort(affectBusinesses.begin(), affectBusinesses.end(), [&](int aId, int bId) {
                return buses[aId].value > buses[bId].value;
            });
        } else {
            //跟java一致，使用稳定排序
            stable_sort(affectBusinesses.begin(), affectBusinesses.end(), [&](int aId, int bId) {
                return buses[aId].value > buses[bId].value;
            });
        }
        int affectSize = int(affectBusinesses.size());


        //3.循环调度,求出最优解保存
        unordered_map<int, vector<Point>> bestResult;
        double bestScore = -1;
        int remainTime = (int) (SEARCH_TIME - 1000 - int(runtime()));//留1s阈值
        int remainMaxCount = max(1, MAX_E_FAIL_COUNT - curHandleCount + 1);
        int maxRunTime = remainTime / remainMaxCount;
        int tmpRemainResource = remainResource;
        int startTime = runtime();
        int iteration = 0;
        bool repeat = false;
        while (iteration == 0 || repeat) {
            int l1 = runtime();
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
            undoResult(satisfyBusesResult, curBusesResult, tmpRemainResource, !IS_ONLINE || test);//回收结果，下次迭代
            iteration++;
            int r1 = runtime();

            //是否重复判断
            if (IS_ONLINE && !test && maxRunTime - (r1 - startTime) - (r1 - l1) > 0) {
                for (int j = 1; j <= N; j++) {
                    shuffle(searchGraph[j].begin(), searchGraph[j].end(), searchRad);
                }
                shuffle(affectBusinesses.begin(), affectBusinesses.end(), searchRad);
                repeat = true;
            } else {
                repeat = false;
            }
            //printError("iteration:" + to_string(iteration) + ",curHandleCount:" + to_string(curHandleCount));
        }
        redoResult(affectBusinesses, bestResult, curBusesResult, !IS_ONLINE || test);
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

        //更新快速跳表
        for (int i = 1; i < edges.size(); i++) {
            Edge &edge = edges[i];
            //计算表
            updateEdgeChannelTable(edge);
        }

        //调整变通道权重
        int totalChangeCount = 0;
        for (int i = 1; i < vertices.size(); i++) {
            Vertex &vertex = vertices[i];
            totalChangeCount += vertex.maxChangeCount;
        }
        //CHANGE_CHANNEL_WEIGHT = EDGE_LENGTH_WEIGHT * (int(edges.size()) - 1) * 2 / totalChangeCount;


        //计算整体资源,通道资源，加变通道资源
        for (int i = 1; i < edges.size(); i++) {
            totalResource += CHANNEL_COUNT * EDGE_LENGTH_WEIGHT;
        }
        for (int i = 1; i < vertices.size(); i++) {
            Vertex &vertex = vertices[i];
            totalResource += CHANGE_CHANNEL_WEIGHT * vertex.maxChangeCount;
        }

        remainResource = totalResource;
        for (int i = 1; i < buses.size(); i++) {
            Business &bus = buses[i];
            remainResource -= calculatesResource(busesOriginResult[bus.id]);
        }
        int totalEdgeValue = 0;
        for (int i = 1; i < edges.size(); i++) {
            for (int j = 1; j <= CHANNEL_COUNT; j++) {
                if (edges[i].channel[j] != -1 && edges[i].channel[j] != edges[i].channel[j - 1]) {
                    totalEdgeValue += buses[edges[i].channel[j]].value;
                }
            }
        }
        avgEdgeAffectValue = 1.0 * totalEdgeValue / (int(edges.size()) - 1);


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
                vector<Point> meFindPath = aStarFindPath(business, originPath,
                                                         EVERY_SCENE_MAX_FAIL_EDGE_COUNT, 1,
                                                         true);
                if (!baseFindPath.empty()) {
                    baseValue += buses[id].value;
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
                dispatch(curBusesResult, failEdgeId, int(sample.size()), j + 1,
                         i != 0, true, false);
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
        int bestMaxLength = int(sample.size());
        for (int i = int(sample.size()) - 1; i >= 0; i--) {
            int diff = ourScore[i] - baseScore[i];
            if (diff > maxValue && checkSatisfiedSamplesSimilarity(otherSamples, tmp)) {
                maxValue = diff;
                bestLength = i;
            }
            tmp.pop_back();
        }
        if (bestLength < int(sample.size()) - 1) {
            //重算
            for (int i = 0; i < 1; i++) {
                vector<vector<Point>> curBusesResult = busesOriginResult;
                int remainValue = totalValue;
                for (int j = 0; j < bestLength + 1; j++) {
                    int failEdgeId = sample[j];
                    vector<int> beforeIds = getAllUnDieBusinessId(failEdgeId);
                    dispatch(curBusesResult, failEdgeId, bestLength + 1, j + 1, false, true, false);
                    for (int beforeId: beforeIds) {
                        if (buses[beforeId].die) {
                            remainValue -= buses[beforeId].value;
                        }
                    }
                    ourScore[j] = remainValue;
                }
                reset();
            }
            tmp = {sample.begin(), sample.begin() + bestLength + 1};
            bool find = false;
            for (int i = bestLength; i >= 0; i--) {
                int diff = ourScore[i] - baseScore[i];
                if (diff > maxValue && checkSatisfiedSamplesSimilarity(otherSamples, tmp)) {
                    maxValue = diff;
                    bestLength = i;
                    find = true;
                }
                tmp.pop_back();
            }
            if (find) {
                bestMaxLength = bestLength + 1;
            }
        }
        vector<int> result;
        result.push_back(bestLength + 1);
        result.push_back(maxValue);
        result.push_back(bestMaxLength);
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
    myGenerate(vector<vector<int>> &beforeSample, int generateInitLength, int candidateEdgeSize,
               const int sampleReturnCount) {
        bool beSelect[edges.size()];
        vector<vector<int>> samples;
        int scores[edges.size()];
        generateInitLength = min(int(edges.size()) - 1, generateInitLength);
        candidateEdgeSize = min(int(edges.size()) - 1, candidateEdgeSize);
        struct EdgeIdScore {
            int id;
            int score;

            bool operator<(const EdgeIdScore &o1) const {
                return score > o1.score;
            }
        };

        int tryCount = 0;
        while (samples.size() < sampleReturnCount) {
            memset(beSelect, false, sizeof beSelect);
            memcpy(scores, createScores, sizeof scores);
            vector<int> sample;
            for (int i = 0; i < generateInitLength; i++) {
                priority_queue<EdgeIdScore> minScoreQ;
                for (int j = 1; j < edges.size(); j++) {
                    if (beSelect[j]) {
                        continue;
                    }
                    if (minScoreQ.size() < candidateEdgeSize) {
                        minScoreQ.push({j, scores[j]});
                        continue;
                    }

                    if (scores[j] > minScoreQ.top().score) {
                        minScoreQ.pop();
                        minScoreQ.push({j, scores[j]});
                    }
                }
                //随机选择一个边断掉
                int index = int(createSampleRad() % candidateEdgeSize);
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
                        scores[point.edgeId] -= buses[busId].value;
                    }
                }
                sample.push_back(id);
            }
            if (checkSatisfiedSamplesSimilarity(beforeSample, sample)) {
                samples.push_back(sample);
            } else {
                tryCount++;
                if (tryCount > CREATE_SHUFFLE_MAX_TRY_COUNT) {
                    if (generateInitLength == 1) {
                        break;
                    }
                    tryCount = 0;
                    generateInitLength = max(1, (int) (generateInitLength * 0.8));
                }
            }
        }
        return samples;
    }

    struct SampleResult {
        int value; //价值
        int maxLength; //价值
        vector<int> sample;//断边序列
        bool operator<(const SampleResult &o) const {
            return value > o.value;
        }
    };

    vector<int> getBestSample(vector<vector<int>> &beforeSamples, vector<vector<int>> &candidateSamples) {
        int bestIndex = -1;
        int bestLength = -1;
        int bestScore = -1000000;
        int bestMaxLength = -1;
        vector<int> result;
        for (int i = 0; i < candidateSamples.size(); i++) {
            vector<int> &candidateSample = candidateSamples[i];
            vector<int> bestLengthAndScore = getBestLengthAndScore(beforeSamples, candidateSample);
            if (bestLengthAndScore[1] > bestScore) {
                bestIndex = i;
                bestLength = bestLengthAndScore[0];
                bestScore = bestLengthAndScore[1];
                bestMaxLength = bestLengthAndScore[2];
            }
        }

        result.push_back(bestIndex);
        result.push_back(bestLength);
        result.push_back(bestScore);
        result.push_back(bestMaxLength);
        return result;
    }

    void
    createBaseSamples(vector<SampleResult> &results, const int candidateSampleCount, const int maxRunTime,
                      int candidateEdgeCount,
                      int generateInitLength) {
        if (results.size() >= CREATE_SAMPLE_COUNT) {
            return;
        }

        vector<vector<int>> curSamples;
        for (const SampleResult &result: results) {
            curSamples.push_back(result.sample);
        }
        candidateEdgeCount = min(candidateEdgeCount, int(edges.size()) - 1);
        generateInitLength = min(generateInitLength, int(edges.size()) - 1);

        int oneMaxRunTime = (int) (maxRunTime - runtime()) / (CREATE_SAMPLE_COUNT - int(results.size()));
        while (results.size() < CREATE_SAMPLE_COUNT) {
            if (runtime() > maxRunTime) {
                break;
            }
            int iterateCount = 0;
            vector<int> bestSample;
            int bestScore = -1;
            int bestLength = -1;
            int startTime = runtime();
            bool repeat = false;
            while (iterateCount == 0 || repeat) {
                int l1 = runtime();
                vector<vector<int>> candidateSamples = myGenerate(curSamples, generateInitLength, candidateEdgeCount,
                                                                  1);
                vector<int> bestSampleIndex = getBestSample(curSamples, candidateSamples);
                vector<int> curSample = {candidateSamples[bestSampleIndex[0]].begin(),
                                         candidateSamples[bestSampleIndex[0]].begin() +
                                         bestSampleIndex[1]};
                int curScore = bestSampleIndex[2];
                int curLength = bestSampleIndex[3];
                if (curScore > bestScore) {
                    bestSample = curSample;
                    bestScore = curScore;
                    bestLength = curLength;
                }
                iterateCount++;
                int r1 = runtime();
                repeat = iterateCount < candidateSampleCount &&
                         oneMaxRunTime - (runtime() - startTime) - (r1 - l1) > 0;
            }

            curSamples.push_back(bestSample);
            results.push_back({bestScore, bestLength, bestSample});
            int totalValue = 0;
            for (const SampleResult &result: results) {
                totalValue += result.value;
            }
            printError("curSize:" + to_string(curSamples.size()) + ",candidateSampleCount:"
                       + to_string(candidateSampleCount) + ",realIterateCount:" + to_string(iterateCount)
                       + ",totalValue:"
                       + to_string(totalValue));
        }
        sort(results.begin(), results.end());
    }

    int optimizeSamples(vector<SampleResult> &results) {
        //优化
        while (true) {
            int minIndex = 0;
            int minValue = results[0].value;
            int minSampleLength = int(results[0].sample.size());
            int maxSampleLength = int(results[0].sample.size());
            for (int i = 1; i < results.size(); i++) {
                if (results[i].value < minValue) {
                    minIndex = i;
                    minValue = results[i].value;
                }
                if (results[i].sample.size() < minSampleLength) {
                    minSampleLength = int(results[i].sample.size());
                }

                if (results[i].sample.size() > maxSampleLength) {
                    maxSampleLength = int(results[i].sample.size());
                }
            }
            vector<vector<int>> tmpSamples;
            for (int i = 0; i < results.size(); i++) {
                if (i != minIndex) {
                    tmpSamples.push_back(results[i].sample);
                }
            }
            int curCreateLength = minSampleLength + int(createSampleRad() % (maxSampleLength -
                                                                             minSampleLength + 2));
            int noBetterCount = 0;
            while (noBetterCount < 2 * CREATE_SAMPLE_COUNT * CREATE_OPTIMIZE_SAMPLE_CANDIDATE_COUNT) {
                vector<vector<int>> candidateSamples = myGenerate(tmpSamples,
                                                                  curCreateLength,
                                                                  CREATE_OPTIMIZE_EDGE_CANDIDATE_COUNT,
                                                                  1);
                if (candidateSamples.empty()) {
                    continue;
                }
                vector<int> bestSampleIndex = getBestSample(tmpSamples, candidateSamples);
                vector<int> bestSample = {candidateSamples[bestSampleIndex[0]].begin(),
                                          candidateSamples[bestSampleIndex[0]].begin() +
                                          bestSampleIndex[1]};
                int bestScore = bestSampleIndex[2];
                int bestLength = bestSampleIndex[3];
                if (bestScore > minValue) {
                    results[minIndex] = {bestScore, bestLength, bestSample};
                    noBetterCount = 0;
                    break;
                } else {
                    noBetterCount++;
                }
                if (runtime() > CREATE_OPTIMIZE_SAMPLES_MAX_TIME) {
                    break;
                }
            }
            if (noBetterCount != 0) {
                break;
            }
            if (runtime() > CREATE_OPTIMIZE_SAMPLES_MAX_TIME) {
                break;
            }
            int totalValue = 0;
            for (const SampleResult &result: results) {
                totalValue += result.value;
            }
            printError("totalValue:" + to_string(totalValue) + ",noBetterCount:" +
                       to_string(noBetterCount));
        }


        //重新基础规划
        int bestValue = 0;
        for (const SampleResult &result: results) {
            bestValue += result.value;
        }
        sort(results.begin(), results.end());

        vector<SampleResult> bestResult = results;
        for (int i = 1; i < bestResult.size(); i++) {
            int initLength = EVERY_SCENE_MAX_FAIL_EDGE_COUNT;
            int popCount = int(createSampleRad() % 2) == 0 ? 1 : 2;
            vector<SampleResult> curResults = bestResult;
            for (int j = 0; j <= i; j++) {
                curResults.pop_back();
            }

            createBaseSamples(curResults, CREATE_OPTIMIZE_SAMPLE_CANDIDATE_COUNT, CREATE_OPTIMIZE_SAMPLES_MAX_TIME,
                              CREATE_OPTIMIZE_EDGE_CANDIDATE_COUNT, initLength);
            if (curResults.size() < bestResult.size()) {
                //超时结束了
                break;
            }
            int newValue = optimizeSamples(curResults);
            if (newValue > bestValue) {
                bestResult = curResults;
                bestValue = newValue;
            }
            if (runtime() > CREATE_OPTIMIZE_SAMPLES_MAX_TIME) {
                break;
            }
        }
        results.swap(bestResult);
        return bestValue;
    }

//主循环
    void mainLoop() {
        // 生成段


        //1.选定最好生成策略
//        vector<SampleResult> results;
//        createBaseSamples(results, CREATE_BASE_SAMPLE_CANDIDATE_COUNT, CREATE_BASE_SAMPLES_MAX_TIME,
//                          CREATE_BASE_EDGE_CANDIDATE_COUNT, EVERY_SCENE_MAX_FAIL_EDGE_COUNT);
//        optimizeSamples(results);
//        vector<vector<int>> curSamples;
//        int shouldValue = 0;
//        for (const SampleResult &result: results) {
//            curSamples.push_back(result.sample);
//            shouldValue += result.value;
//        }
//        printError("shouldValue:" + to_string(shouldValue));
//
//
//        printMeCreateSamples(curSamples);
//// 规划段 本地测试
//        if (LOCAL_TEST_CREATE) {
//            double myScore = 0, baseScore = 0;
//            int myValue = 0, baseValue = 0;
//            for (int i = 0; i < 2; i++) {
//                curScore = 0;
//                for (const auto &result: results) {
//                    auto &curSample = result.sample;
//                    vector<vector<Point>> curBusesResult = busesOriginResult;
//                    for (int k = 0; k < curSample.size(); k++) {
//                        int failEdgeId = curSample[k];
//                        int curLength = k + 1;
//                        if (i == 0) {
//                            dispatch(curBusesResult, failEdgeId, result.maxLength,
//                                     curLength, false, true, true);
//                        } else {
//                            dispatch(curBusesResult, failEdgeId, EVERY_SCENE_MAX_FAIL_EDGE_COUNT,
//                                     curLength, true, true, true);
//                        }
//                    }
//                    //邻接表
//                    int totalValue = 0;
//                    int remainValue = 0;
//                    for (int k = 1; k < buses.size(); k++) {
//                        totalValue += buses[k].value;
//                        if (!buses[k].die) {
//                            remainValue += buses[k].value;
//                        }
//                    }
//                    if (i == 0) {
//                        myValue += remainValue;
//
//                    } else {
//                        baseValue += remainValue;
//                    }
//                    curScore += 10000.0 * remainValue / totalValue;
//                    reset();
//                }
//                if (i == 0) {
//                    myScore = curScore;
//                } else {
//                    baseScore = curScore;
//                }
//            }
//            curScore = (myScore - baseScore);
//            printError(
//                    "totalScore:" + to_string(curSamples.size() * 10000) + ",myScore:" +
//                    to_string(myScore).substr(0, to_string(myScore).length() - 3) +
//                    ",baseScore:" + to_string(baseScore).substr(0, to_string(baseScore).length() - 3) +
//                    ",diffScore:" +
//                    to_string(curScore).substr(0, to_string(curScore).length() - 3)
//                    + ",value:" + to_string(myValue - baseValue));
//
//            return;
//        }

        int t;
        scanf("%d", &t);
        resultScore[0] = 10000.0 * t;
        int maxLength = INT_INF;//每一个测试场景的断边数，默认是无穷个，猜测每次都一样
        for (int i = 0; i < t; i++) {
            //邻接表
            vector<vector<Point>> curBusesResult = busesOriginResult;
            int curLength = 0;
            scanf("%d", &curLength);
            for (int j = 0; j < curLength; ++j) {
                int failEdgeId = -1;
                scanf("%d", &failEdgeId);
                if (failEdgeId == -1) {
                    break;
                }
                dispatch(curBusesResult, failEdgeId, curLength,
                         j + 1, false, false, true);
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
            resultScore[1] += 10000.0 * remainValue / totalValue;
            reset();
        }
    }
};

int main() {
    //    SetConsoleOutputCP ( CP_UTF8 ) ;
//todo 1.生成逻辑可能存在问题,2.可能有bug，再研究研究
    static Strategy strategy;
    if (fopen("../data/0/in.txt", "r") != nullptr) {
        string path = "../data/";
//        MAX_E_FAIL_COUNT = 12000;
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
                       to_string(strategy.resultScore[0]).substr(0, to_string(strategy.resultScore[0]).length() - 3) +
                       ",curScore:" +
                       to_string(strategy.resultScore[1]).substr(0,
                                                                 to_string(strategy.resultScore[1]).length() - 3)
                       + ",time9:" + to_string(time9));
        }
    } else {
        strategy.init();
        strategy.mainLoop();
    }

    return 0;
}
