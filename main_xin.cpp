//
// Created by 16634 on 2024/5/15.
//
#include <iostream>
#include <vector>
#include <fstream>
//#include <string.h>
#include <map>
#include <set>
#include <algorithm>
#include <chrono>
//#include <stdio.h>
using namespace std;



#define  DOUINT  pair<int,int>
struct work{
    int src;                 //业务的起点
    int snk;                 //终点
    int S;                   //经过的边数目
    int L;                   //
    int R;                   //在路径上所有边的占用通道范围L-R(0,3)就代表占了0，1，2，3
    int V;                   //该业务的业务价值
    vector<int> edge_nums;   // 初始状态 S个整数依次表示业务依次经过的路径上的每条边的编号
    vector<int> routes;      // 初始路径点

    bool reset;
    vector<int> old_edge_nums;  //重新规划前
    vector<int> new_edge_nums;  //重新规划后
    set<int> routines;       //寻路时用于存放点的
    work():reset(false){};
};

struct edge{
    int num;                     //边的编号
    DOUINT nodes;                //两端点的编号
    /*通道状态
     * 每次为任务规划新路径后，都要对其经过的边上的通道设成占有
     * 对其原路径上边的通道进行释放
     * */
    vector<bool> pass;
    vector<bool> or_pass;        //初始状态
    map<int,DOUINT> work_pass;
    /*键：任务编号 值：占用带宽（2，5）2，3，4  3个
     * 新路径设置完后，需要将新任务插入进来，并将老路径的删除
     * */
    map<int,DOUINT> or_work_pass;
    /*键：空闲长度 值：空闲起始通道号
     * 每次pass改动，都要运行函数来对其进行更新
     * */
    vector<DOUINT> free_pass;
    set<int> works;              //运行任务
    set<int> or_works;           //初始运行任务
    bool reset;
    edge():reset(false),pass(40){};
    edge(int u, int v){
        nodes.first = u;
        nodes.second = v;
        reset = false;
        pass.resize(40,false);
    };
    void set_pass(int i,int u,int v,bool flag){
        if(flag)
            work_pass[i] = DOUINT(u,v);
        else
            work_pass.erase(i);
        fill(pass.begin()+u, pass.begin()+v,flag);
    }
    bool is_free_pass(int u,int v){
        for(int i=u;i<v+1;i++){
            if(pass[i])
                return false;
        }
        return true;
    }
};

struct node{
    int num;
    map<int,vector<int>> neighbor;
    map<int,vector<int>> ori_neighbor;
    int change_num;
    int ori_change_num;
    node(){};
    node(int num,int change_num):num(num),change_num(change_num){};

};
 /* 注意初始业务并不会变通道；
  * 所有编号都是从 开始，业务的编号和边的编号按照输入顺序递增
  * 注意交互部分的每个测试场景，都是从该初始环境开始;
  * */
int N,M,J,T;
/* N表示图的节点数， M表示图的边数
 * J图上初始运行的业务数
 * T个独立的测试场景
 * */
vector<work> serv;
vector<node> nodes;
vector<edge> edges;
vector<vector<int>> alter_routes;//备选路线
set<int> err_edges;//已经断掉的边
void Readcmd()
{
    cin>>N>>M;
    //对点的编号和变化次数进行初始化
    nodes.resize(N);
    for(int i=0;i<N;++i){
        nodes[i].num = i+1;
        cin >> nodes[i].change_num;
        nodes[i].ori_change_num = nodes[i].change_num;
    }
    //对边的编号和端点和通道状态进行初始化
    edges.resize(M);
    DOUINT tmp_1;
    for(int i=0;i<M;++i){
        cin >> tmp_1.first >> tmp_1.second;
        tmp_1.first --;
        tmp_1.second --;
        edges[i].nodes = tmp_1;
        edges[i].num = i+1;
    }
    cin >> J;
    work tmp_2;
    for(int i=0;i<J;++i){
        cin >> tmp_2.src >>tmp_2.snk>>tmp_2.S>>tmp_2.L>>tmp_2.R>>tmp_2.V;
        tmp_2.src--;tmp_2.snk--;
        tmp_2.L--;tmp_2.R--;
        int e_num;
        for(int j=0;j<tmp_2.S;++j){
            cin >> e_num;
            e_num--;
            tmp_2.edge_nums.push_back(e_num);
        }
        serv.push_back(tmp_2);
        tmp_2.edge_nums.clear();
    }
    cin>>T;

}
inline void ReadFile(ifstream &inputFile){
    inputFile>>N>>M;
    //对点的编号和变化次数进行初始化
    nodes.resize(N);
    for(int i=0;i<N;++i){
        nodes[i].num = i+1;
        inputFile >> nodes[i].change_num;
        nodes[i].ori_change_num = nodes[i].change_num;
    }
    //对边的编号和端点和通道状态进行初始化
    edges.resize(M);
    DOUINT tmp_1;
    for(int i=0;i<M;++i){
        inputFile >> tmp_1.first >> tmp_1.second;
        tmp_1.first --;
        tmp_1.second --;
        edges[i].nodes = tmp_1;
        edges[i].num = i+1;
    }
    inputFile >> J;
    work tmp_2;
    for(int i=0;i<J;++i){
        inputFile >> tmp_2.src >>tmp_2.snk>>tmp_2.S>>tmp_2.L>>tmp_2.R>>tmp_2.V;
        tmp_2.src--;tmp_2.snk--;
        tmp_2.L--;tmp_2.R--;
        int e_num;
        for(int j=0;j<tmp_2.S;++j){
            inputFile >> e_num;
            e_num--;
            tmp_2.edge_nums.push_back(e_num);
        }
        serv.push_back(tmp_2);
        tmp_2.edge_nums.clear();
    }
    inputFile>>T;
}



void dfs(work& w,int cur_node,bool is_new){
    static int count = 0;
    if(is_new)
        count = 0;
    ++count;
    if(count>1000)
        return;
    if(alter_routes.size()>2)
        return;
    if(cur_node == w.snk){
        alter_routes.emplace_back(w.new_edge_nums);
        return;
    }
    for(auto next_node : nodes[cur_node].neighbor){
        if(w.routines.count(next_node.first))
            continue;
        w.routines.insert(next_node.first);
        for(auto e:next_node.second){
            if(err_edges.count(e))
                continue;
            if(edges[e].is_free_pass(w.L,w.R)){
                w.new_edge_nums.push_back(e);
                dfs(w,next_node.first,false);
                w.new_edge_nums.pop_back();
                break;
            }
        }
        w.routines.erase(next_node.first);
    }
}


/*此函数接收一个边，对边当前通道的状态进行更新
 * 将更新free_pass(空闲通道)
 * */
void flash_pass(edge& e){
    int len = 0;
//    int start = 0;
    e.free_pass.clear();
    for(int i=0;i<40;i++){
        if(e.pass[i]){
            if(len != 0) {
                e.free_pass.emplace_back(DOUINT(i - len, len));
                len = 0;
            }
        }
        else{
            ++len;
        }
    }
    if(len!=0)
        e.free_pass.emplace_back(DOUINT(40 - len, len));
    sort(e.free_pass.begin(),e.free_pass.end(),[](DOUINT x,DOUINT y){return x.second>y.second;});
}

void reset(){
    for(auto &e:edges){
        if(e.reset){
            e.reset = false;
            e.pass = e.or_pass;
            e.work_pass = e.or_work_pass;
            e.works = e.or_works;
            flash_pass(e);
        }
    }
    for(auto &n:nodes){
        n.neighbor = n.ori_neighbor;
        n.change_num = n.ori_change_num;
    }
    for(auto &w:serv){
        if(w.reset){
            w.reset = false;
            w.old_edge_nums = w.edge_nums;
//            w.new_routes = w.routes;
        }
    }
}

void init(){
    //设置一下每个点都和哪些点相连
    for(int i=0;i<M;i++){
        nodes[edges[i].nodes.first].neighbor[edges[i].nodes.second].push_back(i);
        nodes[edges[i].nodes.second].neighbor[edges[i].nodes.first].push_back(i);
    }
    //遍历每个任务，对边的属性进行赋值
    for(int i=0;i<J;i++){
        serv[i].routes.push_back(serv[i].src);
        for(auto const &e_num : serv[i].edge_nums){
            edges[e_num].set_pass(i,serv[i].L,serv[i].R+1,true);
            edges[e_num].works.insert(i);
            if(serv[i].routes.back() == edges[e_num].nodes.first){
                serv[i].routes.push_back(edges[e_num].nodes.second);
            }
            else{
                serv[i].routes.push_back(edges[e_num].nodes.first);
            }
        }
        serv[i].routines.insert(serv[i].src);
    }
    for(auto &e:edges){
        e.or_pass = e.pass;
        e.or_work_pass = e.work_pass;
        e.or_works = e.works;
        flash_pass(e);
    }
    for(auto &n:nodes){
        n.ori_neighbor = n.neighbor;
        n.ori_change_num = n.change_num;
    }
    for(auto &w:serv){

        w.old_edge_nums = w.edge_nums;

    }

}

int main(){

//        freopen("in.txt", "r", stdin);
//        freopen("out.txt", "w", stdout);

    ifstream myCin("./in.txt");
    ofstream myCout("out.txt");
    cin.rdbuf(myCin.rdbuf());//打开文件后定向到文件流，用完关闭文件
    cout.rdbuf(myCout.rdbuf());//打开文件后定向到文件流，用完关闭文件
    Readcmd();

//
//    ifstream inputFile("G:/Fpan/ligth2024/testcase1.in");
//    if (!inputFile.is_open()) {
//        std::cerr << "无法打开文件" << std::endl;
//        return 1;
//    }
//    ReadFile(inputFile);



    //初始化
    init();
    // 交互部分

    set<int> err_works;//此次需重新规划任务编号
    int err_edge;//当前断掉的边
    vector<int> suc_works;
    set<int> died_works;//已死掉的业务
    int min_len = 0x0fff;//找到最短路经
    int sel_num;//选择的路径编号
    /*对于一个场景，损失一条边后，需要将当前边上运行的活任务（判断此任务是否在died_works）导入err_works中，
     * 遍历这些任务；为其规划新的路径
     * 规划成功的输出，将原先路径上和新的路径上的边的状态更新（占用通道，运行任务）；
     * 失败的加入到died_works
     * 继续
     * */
    int T1 = 1;
    while(T1--){
        reset();
        err_edge = -2;
        err_edges.clear();
        died_works.clear();

//        while(inputFile>>err_edge){
        while(cin>>err_edge){
            err_works.clear();
            suc_works.clear();
            if(err_edge == -1){
                break;
            }
            err_edge--;
            err_edges.insert(err_edge);
            //对于当前边上跑的任务，看其是否是死任务，因为死任务也会占用边
            for(auto i:edges[err_edge].works){
                if(!died_works.count(i))
                    err_works.insert(i);
            }
            //对受损任务进行新的路径规划，规划失败的加入死亡任务组died_works，成功的加入suc_works
            for(auto w:err_works){
                min_len = 0x0fff;
                sel_num = -1;
                alter_routes.clear();//备选路线清空
                auto start = chrono::steady_clock::now();
                dfs(serv[w],serv[w].src,true);//路径规划，找到路线放入alter_routes
                if(alter_routes.empty()){ //没有找到就死亡
                    died_works.insert(w);
                    continue;
                }
                else{
                    //对每条备选路线进行遍历，找到所需边最少的路径
                    for(int i=0;i<alter_routes.size();i++){
                        if(alter_routes[i].size() < min_len){
                            min_len = alter_routes[i].size();
                            sel_num = i;
                        }
                    }
                }
                serv[w].new_edge_nums = alter_routes[sel_num];//将任务w的所经边进行更新
                //对成功组在原先边上占有通道进行释放，对新占边状态进行更新


                //对新占的边的通道进行占有
                for(auto e : serv[w].new_edge_nums){
                    edges[e].set_pass(w,serv[w].L,serv[w].R+1,true);
                    edges[e].reset = true;//因为对通道状态更新了
                    flash_pass(edges[e]);
                    edges[e].works.insert(w);
                }
                //将当前的路径备份值old_edge_nums

                suc_works.emplace_back(w);//将任务w加入成功组
            }
            //对成功规划的任务进行输出
            cout << suc_works.size()<<endl;
            fflush(stdout);
            for(auto w : suc_works){
                //释放原边通道 edge_nums
                for(auto e : serv[w].old_edge_nums){
                    edges[e].set_pass(w,serv[w].L,serv[w].R+1,false);
                    edges[e].reset = true;//因为对通道状态更新了
                    flash_pass(edges[e]);
                    edges[e].works.erase(w);
                }
                serv[w].old_edge_nums = serv[w].new_edge_nums;
                serv[w].new_edge_nums.clear();
                cout << w+1 << ' ' << serv[w].old_edge_nums.size() << endl;
                fflush(stdout);
                int e;
                for(int i=0;i<serv[w].old_edge_nums.size();++i){
                    e = serv[w].old_edge_nums[i];
                    if(serv[w].old_edge_nums.size()-i==1)
//                        cout << edges[e].num << ' ' <<edges[e].work_pass[w].first+1 << ' ' << edges[e].work_pass[w].second;
                        cout << edges[e].num << ' ' <<serv[w].L+1 << ' ' << serv[w].R+1;
                    else
                        cout << edges[e].num << ' ' <<serv[w].L+1 << ' ' << serv[w].R+1<<' ';
//                        cout << edges[e].num << ' ' <<edges[e].work_pass[w].first+1 << ' ' << edges[e].work_pass[w].second<<' ';
                }
                cout << endl;
                fflush(stdout);
            }


        }

        //恢复初始状态
    }

    int e;
    T--;
    while(T--){
        while(cin >> e){
            cout << 0 <<endl;
            fflush(stdout);
        }
    }
    return 0;
}
//    inputFile.close();
