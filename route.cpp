#include "route.h"
#include "lib/lib_io.h"
#include "lib/lib_record.h"
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <vector>
#include <map>
#include <queue>
#include <algorithm>
#include <unistd.h>

using namespace std;

#define INF 65000
#define JUDGEINF 30000

bool reverseflag = false; //图是否经过反转
int graph[2010][2010];
map<pair<int, int>, int> edgeidx;
int srcNode;
int dstNode;
vector<int> midNode;
int nodeNum;
int midNodeNum;

int globalminweight = INF;
int globalminpath[2010];

map<int, int> mid2all;
map<int, int> all2mid;

int mid_dis[110][110];
vector<pair<int, int> > coll[110][110];
vector<int> mid_path[110][110];

bool is_connect[110][110]; //record the connection of mid node
int indegree[110];
int outdegree[110];
int mid_path_set_next[110];
int mid_path_set_prev[110];

vector<int> ans;

//dijkstra
int dis[2010];
bool done[2010];
int dijkprev[2010];

//search mode
#define TYPE_INOUTDEGREE 0
#define TYPE_INDEGREE 1
#define MODE_NORMAL 0
#define MODE_SORT 1
#define MODE_BUG_NORMAL_EDGEWEI 2
#define MODE_NORMAL_EDGEWEI 3
#define MODE_NORMAL_OUTDEGREE 4
#define MODE_NORMAL_INDEGREE 4
int search_type = TYPE_INDEGREE;
int search_mode = MODE_NORMAL;
int search_wide = INF;

void jbdijkstra(int s)
{
    //dijkstra
    memset(done, 0, sizeof(bool)*nodeNum);
    memset(dijkprev, -1, sizeof(int)*nodeNum);
    for(int i = 0; i < nodeNum; i++)
        dis[i] = INF;
    priority_queue<pair<long long,int> , vector<pair<long long,int> >, greater<pair<long long,int> > > que;
    dis[s] = 0;
    que.push(make_pair(dis[s], s));
    while(!que.empty())
    {
        pair<long long,int> v = que.top();
        que.pop();
        if(done[v.second]) continue;
        done[v.second] = true;
        //v点已经完全确定
        if(dijkprev[v.second] != -1)
        {
            if(find(midNode.begin(), midNode.end(), v.second) != midNode.end()) //是中间节点
            {
                continue; //中间节点不继续往后更新
            }
        }
        for(int i = 0; i < nodeNum; i++)
        {
            int u = i;
            if(dis[u] > dis[v.second] + graph[v.second][u])
            {
                dijkprev[u] = v.second;
                dis[u] = dis[v.second] + graph[v.second][u];
                que.push(make_pair(dis[u], u));
            }
        }
    }
    return;
}

void graphinit(char* topo[5000], int edge_num)
{

    //init graph
    for(int i = 0; i < 2010; i++)
    {
        //memset(graph[i], 63, sizeof(graph[i]));
        for(int j = 0; j < 2010; j++)
        {
            graph[i][j] = INF;
        }
    }
    nodeNum = 0;
    for(int i = 0; i < edge_num; i++)
    {
        char* str = topo[i];
        //de(str);
        char* token;
        token = strtok(str, ",");
        int idx = atoi(token);
        token = strtok(NULL, ",");
        int src = atoi(token);
        token = strtok(NULL, ",");
        int dst = atoi(token);
        token = strtok(NULL, ",");
        int wei = atoi(token);
        if(graph[src][dst] > wei)
        {
            graph[src][dst] = wei;
            edgeidx[make_pair(src, dst)] = idx;
        }
        if(src > nodeNum) nodeNum = src;
        if(dst > nodeNum) nodeNum = dst;
        //printf("Add edge: idx %d, %d -> %d, weight %d\n",  idx, src, dst, wei);
    }
    nodeNum++;
}

void init(char *demand)
{
    ans.clear();
    reverseflag = false;
    globalminweight = INF;
    midNodeNum = 0;
    midNode.clear();
    mid2all.clear();
    all2mid.clear();

    //printf("Node num: %d\n", nodeNum);
    //de(demand);
    char* token;
    token = strtok(demand, ",");
    token = strtok(NULL, ",");
    srcNode = atoi(token);
    token = strtok(NULL, ",");
    dstNode = atoi(token);
    //printf("SrcNode: %d, DstNode: %d\n", srcNode, dstNode);
    token = strtok(NULL, ",");
    //de(token);
    char *subtoken;
    subtoken = strtok(token, "|" );
    //de(subtoken);
    //printf("MidNode:");
    while(subtoken != NULL)
    {
        int tempmidnode = atoi(subtoken);
        if(tempmidnode > nodeNum) nodeNum = tempmidnode; //中间节点号可能比图的大(孤立)
        midNode.push_back(tempmidnode);
        mid2all[midNodeNum] = tempmidnode;
        all2mid[tempmidnode] = midNodeNum;
        midNodeNum++;
        //printf(" %d", atoi(subtoken));
        subtoken = strtok( NULL, "|" );
   }
   //printf(", count %d\n", midNodeNum);
}

void jbinit(int type, int mode, int wide)
{
    search_type = type;
    search_mode = mode;
    search_wide = wide;
/*
    for(int i = 0; i < nodeNum; i++)
    {
        graph[dstNode][i] = INF;
        graph[i][srcNode] = INF;
    }
*/
    for(int i = 0; i <= midNodeNum; i++)
        memset(is_connect[i], 0, sizeof(bool)*(midNodeNum + 1));
    memset(indegree, 0, sizeof(int)*(midNodeNum + 1));
    memset(outdegree, 0, sizeof(int)*(midNodeNum + 1));
    memset(mid_path_set_next, -1, sizeof(int)*(midNodeNum + 1));
    memset(mid_path_set_prev, -1, sizeof(int)*(midNodeNum + 1));

    vector<pair<int, int> > tempcoll[2010][2];

    for(int i = 0; i < 110; i++)
    {
        for(int j = 0; j < 110; j++)
        {
            mid_dis[i][j] = INF;
            coll[i][j].clear();
            mid_path[i][j].clear();
        }
    }

    for(int i = 0; i < midNodeNum; i++)
    {
        int alli = mid2all[i];
        jbdijkstra(alli);
        for(int j = 0; j < midNodeNum; j++)
        {
            if(i == j)
            {
                mid_dis[i][j] = INF;
                is_connect[i][j] = false;
                continue;
            }
            int allj = mid2all[j];
            mid_dis[i][j] = dis[allj];
            if(mid_dis[i][j] < JUDGEINF)
            {
                is_connect[i][j] = true;
                outdegree[i]++;
                indegree[j]++;

                int pathptr = allj;
                tempcoll[pathptr][0].push_back(make_pair(i, j));
                mid_path[i][j].push_back(pathptr);
                pathptr = dijkprev[pathptr];
                while(dijkprev[pathptr] != -1)
                {
                    tempcoll[pathptr][0].push_back(make_pair(i, j));
                    tempcoll[pathptr][1].push_back(make_pair(i, j));
                    mid_path[i][j].push_back(pathptr);
                    pathptr = dijkprev[pathptr];
                }
                tempcoll[pathptr][1].push_back(make_pair(i, j));
                mid_path[i][j].push_back(pathptr);
            }
        }

        mid_dis[i][midNodeNum] = dis[dstNode];
        if(mid_dis[i][midNodeNum] < JUDGEINF)
        {
            is_connect[i][midNodeNum] = true;
            indegree[midNodeNum]++;
            outdegree[i]++;

            int pathptr = dstNode;
            tempcoll[pathptr][0].push_back(make_pair(i, midNodeNum));
            mid_path[i][midNodeNum].push_back(pathptr);
            pathptr = dijkprev[pathptr];
            while(dijkprev[pathptr] != -1)
            {
                tempcoll[pathptr][0].push_back(make_pair(i, midNodeNum));
                tempcoll[pathptr][1].push_back(make_pair(i, midNodeNum));
                mid_path[i][midNodeNum].push_back(pathptr);
                pathptr = dijkprev[pathptr];
            }
            tempcoll[pathptr][1].push_back(make_pair(i, midNodeNum));
            mid_path[i][midNodeNum].push_back(pathptr);
        }
    }
    jbdijkstra(srcNode);
    for(int j = 0; j < midNodeNum; j++)
    {
        int allj = mid2all[j];
        mid_dis[midNodeNum][j] = dis[allj];
        if(mid_dis[midNodeNum][j] < JUDGEINF)
        {
            is_connect[midNodeNum][j] = true;
            indegree[j]++;
            outdegree[midNodeNum]++;

            int pathptr = allj;
            tempcoll[pathptr][0].push_back(make_pair(midNodeNum, j));
            mid_path[midNodeNum][j].push_back(pathptr);
            pathptr = dijkprev[pathptr];
            while(dijkprev[pathptr] != -1)
            {
                tempcoll[pathptr][0].push_back(make_pair(midNodeNum, j));
                tempcoll[pathptr][1].push_back(make_pair(midNodeNum, j));
                mid_path[midNodeNum][j].push_back(pathptr);
                pathptr = dijkprev[pathptr];
            }
            tempcoll[pathptr][1].push_back(make_pair(midNodeNum, j));
            mid_path[midNodeNum][j].push_back(pathptr);
        }
    }

    for(int i = 0; i < nodeNum; i++)
    {
        for(int l = 0; l < 2; l++)
        {
            for(unsigned int j = 0; j < tempcoll[i][l].size(); j++)
            {
                for(unsigned int k = 0; k < tempcoll[i][l].size(); k++)
                {
                    if(j == k) continue;
                    vector<pair<int, int> > tempvec = coll[tempcoll[i][l][j].first][tempcoll[i][l][j].second];
                    if(find(tempvec.begin(), tempvec.end(), tempcoll[i][l][k]) == tempvec.end())
                        coll[tempcoll[i][l][j].first][tempcoll[i][l][j].second].push_back(tempcoll[i][l][k]);
                }
            }
        }
    }

    for(int i = 0; i <= midNodeNum; i++)
    {
        for(int j = 0; j <= midNodeNum; j++)
        {
            if(i == j) continue;
            coll[i][j].push_back(make_pair(j, i));
        }
    }
}

bool compareidxdis(pair<int, int> a, pair<int, int> b)
{
    return a.second < b.second;
}

bool can_jbsearch(int u, int v)
{
    if(!is_connect[u][v]) return false; //这条边已经被删了

    //检查是否之前已经访问过
    if(mid_path_set_next[u] != -1) return false;
    if(mid_path_set_prev[v] != -1) return false;

    //检查提前成环
    int cnt = 0;
    int ptr = v;
    while(ptr != -1)
    {
        cnt++;
        if(ptr == u && cnt != midNodeNum + 1) return false;
        ptr = mid_path_set_next[ptr];
    }

    //检查删边后是否会让某一未访问的点出入度为0
    int tempindegree[110]; int tempoutdegree[110];
    memcpy(tempindegree, indegree, sizeof(int)*(midNodeNum + 1));
    memcpy(tempoutdegree, outdegree, sizeof(int)*(midNodeNum + 1));
    for(vector<pair<int, int> >::iterator it = coll[u][v].begin(); it != coll[u][v].end(); it++)
    {
        if(!is_connect[(*it).first][(*it).second]) continue; //已经删过的就不删了
        tempindegree[(*it).second]--;
        tempoutdegree[(*it).first]--;
    }
    for(int i = 0; i <= midNodeNum; i++)
    {
        if(mid_path_set_next[i] != -1 && tempoutdegree[i] <= 0) //出度不合格
        {
            if(i != u) return false;
        }
        if(mid_path_set_prev[i] != -1 && tempindegree[i] <= 0) //入度不合格
        {
            if(i != v) return false;
        }
    }

    return true;
}

void modify_jbsearch(int u, int v)
{
    mid_path_set_next[u] = v;
    mid_path_set_prev[v] = u;

    for(vector<pair<int, int> >::iterator it = coll[u][v].begin(); it != coll[u][v].end(); it++)
    {
        if(!is_connect[(*it).first][(*it).second]) continue; //已经删过的就不删了
        indegree[(*it).second]--;
        outdegree[(*it).first]--;
        is_connect[(*it).first][(*it).second] = false;
    }
}

void jbsearch(int lev, int tempans, bool finish)
{
    if(finish) return;
    if(tempans >= globalminweight) return;
    if(lev == midNodeNum + 1) //solved
    {
        if(tempans < globalminweight)
        {
            globalminweight = tempans;
            int ptrp = midNodeNum, ptrq = mid_path_set_next[midNodeNum];
            do
            {
                vector<int> temppath = mid_path[ptrp][ptrq];
                for(vector<int>::iterator it = temppath.end() -1; it > temppath.begin(); it--)
                {
                    ans.push_back(edgeidx[pair<int, int>(*it, *(it-1))]);
                }
                ptrp = ptrq; ptrq = mid_path_set_next[ptrq];
            } while(ptrp != midNodeNum);
            finish = true;
            return;
        }
    }

    //search
    if(search_type)
    {
        //indegree search
        int minindegree = INF, minindegreepos = -1;
        if(search_mode == MODE_NORMAL || search_mode == MODE_NORMAL_INDEGREE)
        {
            for(int i = 0; i <= midNodeNum; i++)
            {
                if(mid_path_set_prev[i] != -1) continue;
                if(indegree[i] < minindegree)
                {
                    minindegree = indegree[i];
                    minindegreepos = i;
                }
            }
        }
        else if(search_mode == MODE_SORT)
        {
            pair<int, int> idxide[110];
            int decnt = 0;
            for(int i = 0; i <= midNodeNum; i++)
            {
                if(mid_path_set_prev[i] != -1) continue;
                idxide[decnt++] = make_pair(i, indegree[i]);
            }
            if(decnt != 0)
            {
                sort(idxide, idxide + decnt, compareidxdis);
                minindegreepos = idxide[0].first;
                minindegree = idxide[0].second;
            }
        }
        else if(search_mode == MODE_BUG_NORMAL_EDGEWEI)
        {
            int minedgeweight = INF;
            for(int i = 0; i <= midNodeNum; i++)
            {
                if(mid_path_set_prev[i] != -1) continue;
                if(indegree[i] < minindegree)
                {
                    for(int j = 0; j <= midNodeNum; j++)
                    {
                        if(i == j) continue;
                        if(is_connect[j][i] && mid_dis[j][i] < minedgeweight)
                        {
                            minedgeweight =  mid_dis[j][i];
                            minindegree = indegree[i];
                            minindegreepos = i;
                        }
                    }
                }
            }
        }
        else if(search_mode == MODE_NORMAL_EDGEWEI)
        {
            int minedgeweight = INF;
            for(int i = 0; i <= midNodeNum; i++)
            {
                if(mid_path_set_prev[i] != -1) continue;
                if(indegree[i] < minindegree)
                {
                        minindegree = indegree[i];
                        minindegreepos = i;
                        minedgeweight = INF;
                }
                if(indegree[i] == minindegree)
                {
                    for(int j = 0; j <= midNodeNum; j++)
                    {
                        if(i == j) continue;
                        if(is_connect[j][i] && mid_dis[j][i] < minedgeweight)
                        {
                            minedgeweight =  mid_dis[j][i];
                            minindegree = indegree[i];
                            minindegreepos = i;
                        }
                    }
                }
            }
        }
        else if(search_mode == MODE_NORMAL_OUTDEGREE)
        {
            int minoutdegree = INF;
            for(int i = 0; i <= midNodeNum; i++)
            {
                if(mid_path_set_prev[i] != -1) continue;
                if(indegree[i] < minindegree)
                {
                        minindegree = indegree[i];
                        minindegreepos = i;
                        minoutdegree = INF;
                }
                if(indegree[i] == minindegree)
                {
                    if(outdegree[i] < minoutdegree)
                    {
                        minoutdegree =  outdegree[i];
                        minindegree = indegree[i];
                        minindegreepos = i;
                    }
                }
            }
        }

        if(minindegreepos == -1) return;

        int edgecnt = 0;
        pair<int, int> idxdis[110];
        for(int j = 0; j <= midNodeNum; j++)
        {
            if(is_connect[j][minindegreepos])
            {
                idxdis[edgecnt++] = make_pair(j, mid_dis[j][minindegreepos]);
            }
        }
        sort(idxdis, idxdis + edgecnt, compareidxdis);
        if(edgecnt>search_wide) edgecnt = search_wide;

        for(int j = 0; j < edgecnt; j++)
        {
            int u = idxdis[j].first, v = minindegreepos;
            if(!can_jbsearch(u, v)) continue;

            //backup
            bool is_connect_copy[110][110];
            int indegree_copy[110];
            int outdegree_copy[110];
            //int mid_path_set_next_copy[110];
            //int mid_path_set_prev_copy[110];
            for(int l = 0; l <= midNodeNum; l++)
                memcpy(is_connect_copy[l], is_connect[l], sizeof(int)*(midNodeNum+1));
            memcpy(indegree_copy, indegree, sizeof(int)*(midNodeNum+1));
            memcpy(outdegree_copy, outdegree, sizeof(int)*(midNodeNum+1));
            //memcpy(mid_path_set_next_copy, mid_path_set_next, sizeof(int)*(midNodeNum+1));
            //memcpy(mid_path_set_prev_copy, mid_path_set_prev, sizeof(int)*(midNodeNum+1));

            //modify
            modify_jbsearch(u, v);

            jbsearch(lev + 1, tempans + mid_dis[u][v], finish);

            //recovery
            for(int l = 0; l <= midNodeNum; l++)
                memcpy(is_connect[l], is_connect_copy[l], sizeof(int)*(midNodeNum+1));
            memcpy(indegree, indegree_copy, sizeof(int)*(midNodeNum+1));
            memcpy(outdegree, outdegree_copy, sizeof(int)*(midNodeNum+1));
            //memcpy(mid_path_set_next, mid_path_set_next_copy, sizeof(int)*(midNodeNum+1));
            //memcpy(mid_path_set_prev, mid_path_set_prev_copy, sizeof(int)*(midNodeNum+1));
            mid_path_set_next[u] = -1;
            mid_path_set_prev[v] = -1;
        }
    }
    else
    {
        //inoutdegree search
        int mininoutdegree = INF, mininoutdegreepos = -1;
        int inflag = -1; //标识是否是添加一条出边
        if(search_mode == MODE_NORMAL)
        {
            for(int i = 0; i <= midNodeNum; i++)
            {
                if(mid_path_set_prev[i] != -1 && mid_path_set_next[i] != -1) continue;
                else if(mid_path_set_prev[i] == -1 && mid_path_set_next[i] == -1) //出入边都没有
                {
                    if(indegree[i] <= outdegree[i]) //取入边
                    {
                        if(indegree[i] < mininoutdegree)
                        {
                            mininoutdegree = indegree[i];
                            mininoutdegreepos = i;
                            inflag = 1;
                        }
                    }
                    else //取出边
                    {
                        if(outdegree[i] < mininoutdegree)
                        {
                            mininoutdegree = outdegree[i];
                            mininoutdegreepos = i;
                            inflag = 0;
                        }
                    }
                }
                else if(mid_path_set_next[i] == -1) //只是没有出边
                {
                    if(outdegree[i] < mininoutdegree) //取出边
                    {
                        mininoutdegree = outdegree[i];
                        mininoutdegreepos = i;
                        inflag = 0;
                    }
                }
                else //只是没有入边
                {
                    if(indegree[i] < mininoutdegree) //取入边
                    {
                        mininoutdegree = indegree[i];
                        mininoutdegreepos = i;
                        inflag = 1;
                    }
                }
            }
        }
        else if(search_mode == MODE_SORT)
        {
            bool inflagarr[110];
            memset(inflagarr, 0, sizeof(bool) * (midNodeNum+1));
            pair<int, int> idxide[110];
            int decnt = 0;
            for(int i = 0; i <= midNodeNum; i++)
            {
                if(mid_path_set_prev[i] != -1 && mid_path_set_next[i] != -1) continue;
                else if(mid_path_set_prev[i] == -1 && mid_path_set_next[i] == -1) //出入边都没有
                {
                    if(indegree[i] <= outdegree[i]) //取入边
                    {
                        if(indegree[i] <= mininoutdegree)
                        {
                            idxide[decnt++] = make_pair(i, indegree[i]);
                            inflagarr[i] = 1;
                        }
                    }
                    else //取出边
                    {
                        if(outdegree[i] <= mininoutdegree)
                        {
                            idxide[decnt++] = make_pair(i, outdegree[i]);
                            inflagarr[i] = 0;
                        }
                    }
                }
                else if(mid_path_set_next[i] == -1) //只是没有出边
                {
                    if(outdegree[i] <= mininoutdegree) //取出边
                    {
                        idxide[decnt++] = make_pair(i, outdegree[i]);
                        inflagarr[i] = 0;
                    }
                }
                else //只是没有入边
                {
                    if(indegree[i] <= mininoutdegree) //取入边
                    {
                        idxide[decnt++] = make_pair(i, indegree[i]);
                        inflagarr[i] = 1;
                    }
                }
            }
            if(decnt != 0)
            {
                sort(idxide, idxide + decnt, compareidxdis);
                mininoutdegreepos = idxide[0].first;
                mininoutdegree = idxide[0].second;
                inflag = inflagarr[mininoutdegreepos];
            }
        }
        else if(search_mode == MODE_BUG_NORMAL_EDGEWEI)
        {
            int minedgeweight = INF;
            for(int i = 0; i <= midNodeNum; i++)
            {
                if(mid_path_set_prev[i] != -1 && mid_path_set_next[i] != -1) continue;
                else if(mid_path_set_prev[i] == -1 && mid_path_set_next[i] == -1) //出入边都没有
                {
                    if(indegree[i] <= outdegree[i]) //取入边
                    {
                        if(indegree[i] <= mininoutdegree)
                        {
                            for(int j = 0; j <= midNodeNum; j++)
                            {
                                if(i == j) continue;
                                if(is_connect[j][i] && mid_dis[j][i] < minedgeweight)
                                {
                                    minedgeweight =  mid_dis[j][i];
                                    mininoutdegree = indegree[i];
                                    mininoutdegreepos = i;
                                    inflag = 1;
                                }
                            }
                        }
                    }
                    else //取出边
                    {
                        if(outdegree[i] <= mininoutdegree)
                        {
                            for(int j = 0; j <= midNodeNum; j++)
                            {
                                if(i == j) continue;
                                if(is_connect[i][j] && mid_dis[i][j] < minedgeweight)
                                {
                                    minedgeweight =  mid_dis[i][j];
                                    mininoutdegree = outdegree[i];
                                    mininoutdegreepos = i;
                                    inflag = 0;
                                }
                            }
                        }
                    }
                }
                else if(mid_path_set_next[i] == -1) //只是没有出边
                {
                    if(outdegree[i] <= mininoutdegree) //取出边
                    {
                        for(int j = 0; j <= midNodeNum; j++)
                        {
                            if(i == j) continue;
                            if(is_connect[i][j] && mid_dis[i][j] < minedgeweight)
                            {
                                minedgeweight =  mid_dis[i][j];
                                mininoutdegree = outdegree[i];
                                mininoutdegreepos = i;
                                inflag = 0;
                            }
                        }
                    }
                }
                else //只是没有入边
                {
                    if(indegree[i] <= mininoutdegree) //取入边
                    {
                        for(int j = 0; j <= midNodeNum; j++)
                        {
                            if(i == j) continue;
                            if(is_connect[j][i] && mid_dis[j][i] < minedgeweight)
                            {
                                minedgeweight =  mid_dis[j][i];
                                mininoutdegree = indegree[i];
                                mininoutdegreepos = i;
                                inflag = 1;
                            }
                        }
                    }
                }
            }
        }
        else if(search_mode == MODE_NORMAL_EDGEWEI)
        {
            int minedgeweight = INF;
            for(int i = 0; i <= midNodeNum; i++)
            {
                if(mid_path_set_prev[i] != -1 && mid_path_set_next[i] != -1) continue;
                else if(mid_path_set_prev[i] == -1 && mid_path_set_next[i] == -1) //出入边都没有
                {
                    if(indegree[i] <= outdegree[i]) //取入边
                    {
                        if(indegree[i] < mininoutdegree)
                        {
                            mininoutdegree = indegree[i];
                            mininoutdegreepos = i;
                            inflag = 1;
                        }
                        if(indegree[i] == mininoutdegree)
                        {
                            for(int j = 0; j <= midNodeNum; j++)
                            {
                                if(i == j) continue;

                                if(is_connect[j][i] && mid_dis[j][i] < minedgeweight)
                                {
                                    minedgeweight =  mid_dis[j][i];
                                    mininoutdegree = indegree[i];
                                    mininoutdegreepos = i;
                                    inflag = 1;
                                }
                            }
                        }
                    }
                    else //取出边
                    {
                        if(outdegree[i] < mininoutdegree)
                        {
                                mininoutdegree = outdegree[i];
                                mininoutdegreepos = i;
                                inflag = 0;
                        }
                        if(outdegree[i] == mininoutdegree)
                        {
                            for(int j = 0; j <= midNodeNum; j++)
                            {
                                if(i == j) continue;
                                if(is_connect[i][j] && mid_dis[i][j] < minedgeweight)
                                {
                                    minedgeweight =  mid_dis[i][j];
                                    mininoutdegree = outdegree[i];
                                    mininoutdegreepos = i;
                                    inflag = 0;
                                }
                            }
                        }
                    }
                }
                else if(mid_path_set_next[i] == -1) //只是没有出边
                {
                    if(outdegree[i] < mininoutdegree) //取出边
                    {
                            mininoutdegree = outdegree[i];
                            mininoutdegreepos = i;
                            inflag = 0;
                    }
                    if(outdegree[i] == mininoutdegree)
                    {
                        for(int j = 0; j <= midNodeNum; j++)
                        {
                            if(i == j) continue;
                            if(is_connect[i][j] && mid_dis[i][j] < minedgeweight)
                            {
                                minedgeweight =  mid_dis[i][j];
                                mininoutdegree = outdegree[i];
                                mininoutdegreepos = i;
                                inflag = 0;
                            }
                        }
                    }
                }
                else //只是没有入边
                {
                    if(indegree[i] < mininoutdegree) //取入边
                    {
                        mininoutdegree = indegree[i];
                        mininoutdegreepos = i;
                        inflag = 1;
                    }
                    if(indegree[i] == mininoutdegree)
                    {
                        for(int j = 0; j <= midNodeNum; j++)
                        {
                            if(i == j) continue;

                            if(is_connect[j][i] && mid_dis[j][i] < minedgeweight)
                            {
                                minedgeweight =  mid_dis[j][i];
                                mininoutdegree = indegree[i];
                                mininoutdegreepos = i;
                                inflag = 1;
                            }
                        }
                    }
                }
            }
        }
        else if(search_mode == MODE_NORMAL_OUTDEGREE)
        {
            for(int i = 0; i <= midNodeNum; i++)
            {
                if(mid_path_set_prev[i] != -1 && mid_path_set_next[i] != -1) continue;
                else if(mid_path_set_prev[i] == -1 && mid_path_set_next[i] == -1) //出入边都没有
                {
                    if(indegree[i] <= outdegree[i]) //取入边
                    {
                        if(indegree[i] <= mininoutdegree)
                        {
                            if(indegree[i] == mininoutdegree && inflag == 0) continue;
                            mininoutdegree = indegree[i];
                            mininoutdegreepos = i;
                            inflag = 1;
                        }
                    }
                    else //取出边
                    {
                        if(outdegree[i] <= mininoutdegree)
                        {
                            if(outdegree[i] == mininoutdegree && inflag == 0) continue;
                            mininoutdegree = outdegree[i];
                            mininoutdegreepos = i;
                            inflag = 0;
                        }
                    }
                }
                else if(mid_path_set_next[i] == -1) //只是没有出边
                {
                    if(outdegree[i] <= mininoutdegree) //取出边
                    {
                        if(outdegree[i] == mininoutdegree && inflag == 0) continue;
                        mininoutdegree = outdegree[i];
                        mininoutdegreepos = i;
                        inflag = 0;
                    }
                }
                else //只是没有入边
                {
                    if(indegree[i] <= mininoutdegree) //取入边
                    {
                        if(indegree[i] == mininoutdegree && inflag == 0) continue;
                        mininoutdegree = indegree[i];
                        mininoutdegreepos = i;
                        inflag = 1;
                    }
                }
            }
        }
        else if(search_mode == MODE_NORMAL_INDEGREE)
        {
            for(int i = 0; i <= midNodeNum; i++)
            {
                if(mid_path_set_prev[i] != -1 && mid_path_set_next[i] != -1) continue;
                else if(mid_path_set_prev[i] == -1 && mid_path_set_next[i] == -1) //出入边都没有
                {
                    if(indegree[i] <= outdegree[i]) //取入边
                    {
                        if(indegree[i] <= mininoutdegree)
                        {
                            if(indegree[i] == mininoutdegree && inflag == 1) continue;
                            mininoutdegree = indegree[i];
                            mininoutdegreepos = i;
                            inflag = 1;
                        }
                    }
                    else //取出边
                    {
                        if(outdegree[i] <= mininoutdegree)
                        {
                            if(outdegree[i] == mininoutdegree && inflag == 1) continue;
                            mininoutdegree = outdegree[i];
                            mininoutdegreepos = i;
                            inflag = 0;
                        }
                    }
                }
                else if(mid_path_set_next[i] == -1) //只是没有出边
                {
                    if(outdegree[i] <= mininoutdegree) //取出边
                    {
                        if(outdegree[i] == mininoutdegree && inflag == 1) continue;
                        mininoutdegree = outdegree[i];
                        mininoutdegreepos = i;
                        inflag = 0;
                    }
                }
                else //只是没有入边
                {
                    if(indegree[i] <= mininoutdegree) //取入边
                    {
                        if(indegree[i] == mininoutdegree && inflag == 1) continue;
                        mininoutdegree = indegree[i];
                        mininoutdegreepos = i;
                        inflag = 1;
                    }
                }
            }
        }

        if(mininoutdegreepos == -1) return;

        int edgecnt = 0;
        pair<int, int> idxdis[110];
        for(int j = 0; j <= midNodeNum; j++)
        {
            if(inflag)
            {
                if(is_connect[j][mininoutdegreepos])
                {
                    idxdis[edgecnt++] = make_pair(j, mid_dis[j][mininoutdegreepos]);
                }
            }
            else
            {
                if(is_connect[mininoutdegreepos][j])
                {
                    idxdis[edgecnt++] = make_pair(j, mid_dis[mininoutdegreepos][j]);
                }
            }
        }
        sort(idxdis, idxdis + edgecnt, compareidxdis);
        if(edgecnt>search_wide) edgecnt = search_wide;

        for(int j = 0; j < edgecnt; j++)
        {
            int u = -1, v = -1;
            if(inflag)
            {
                    u = idxdis[j].first; v = mininoutdegreepos;
            }
            else
            {
                    u = mininoutdegreepos; v = idxdis[j].first;
            }
            if(!can_jbsearch(u, v)) continue;

            //backup
            bool is_connect_copy[110][110];
            int indegree_copy[110];
            int outdegree_copy[110];
            //int mid_path_set_next_copy[110];
            //int mid_path_set_prev_copy[110];
            for(int l = 0; l <= midNodeNum; l++)
                memcpy(is_connect_copy[l], is_connect[l], sizeof(int)*(midNodeNum+1));
            memcpy(indegree_copy, indegree, sizeof(int)*(midNodeNum+1));
            memcpy(outdegree_copy, outdegree, sizeof(int)*(midNodeNum+1));
            //memcpy(mid_path_set_next_copy, mid_path_set_next, sizeof(int)*(midNodeNum+1));
            //memcpy(mid_path_set_prev_copy, mid_path_set_prev, sizeof(int)*(midNodeNum+1));

            //modify
            modify_jbsearch(u, v);

            jbsearch(lev + 1, tempans + mid_dis[u][v], finish);

            //recovery
            for(int l = 0; l <= midNodeNum; l++)
                memcpy(is_connect[l], is_connect_copy[l], sizeof(int)*(midNodeNum+1));
            memcpy(indegree, indegree_copy, sizeof(int)*(midNodeNum+1));
            memcpy(outdegree, outdegree_copy, sizeof(int)*(midNodeNum+1));
            //memcpy(mid_path_set_next, mid_path_set_next_copy, sizeof(int)*(midNodeNum+1));
            //memcpy(mid_path_set_prev, mid_path_set_prev_copy, sizeof(int)*(midNodeNum+1));
            mid_path_set_next[u] = -1;
            mid_path_set_prev[v] = -1;
        }
    }
}

void search_route(char *topo[MAX_EDGE_NUM], int edge_num, char *demand[MAX_DEMAND_NUM], int demand_num)
{
    vector<int> ans1;
    graphinit(topo, edge_num);
    for(int i = 0; i < demand_num; i++)
    {
        init(demand[i]);
        jbinit(TYPE_INDEGREE, MODE_SORT, 2);
        jbsearch(0, 0, false);
        if(i == 0) ans1 = ans;
    }
    for (unsigned int i = 0; i < ans1.size(); i++)
    {
        record_result(WORK_PATH, ans1[i]);
    }
    for (unsigned int i = 0; i < ans.size(); i++)
    {
        record_result(BACK_PATH, ans[i]);
    }
}



