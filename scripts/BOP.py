__author__ = 'Mark'
import sys
from collections import defaultdict, deque
import itertools

sys.setrecursionlimit(20000)

def construct_fragmented_breakpoint_graph(A, B, n):
    V = [0]
    for i in range(1, n):
        V.append(i)
        V.append(-i)
    V.append(-n)
    #Красим вершины. 0 - красная, 1 - белая, 2 - черная, 3 - серая
    colors_dict = defaultdict(int)
    for x in A:
        if len(x) >= 1:
            colors_dict[x[-1]] += 1
        colors_dict[-x[0]] += 1

    for x in B:
        if len(x) >= 1:
            colors_dict[x[-1]] += 2
        colors_dict[-x[0]] += 2

    colors = []
    for x in V:
        colors.append(colors_dict[x])

    fragmented_graph = defaultdict(list)
    for x in itertools.chain(A, B):
        for i in range(len(x) - 1):
            fragmented_graph[x[i]].append(-x[i+1])
            fragmented_graph[-x[i+1]].append(x[i])
    return V, colors, fragmented_graph


def construct_block_ordering_graph(V, colors, F, A, B):
    was = defaultdict(int)
    def dfs(v):
        was[v] = 1
        for x in F[v]:
            if not was[x]:
                return dfs(x)
        return v


    #вершины в BOG, 0 - белая, 1 - черная
    newV = []
    #1 - ребра между концами путей и смежными вершинами, 0 - ребра между концами
    #компонент
    block_ordering_graph = defaultdict(list)
    vertex_colors = defaultdict(list)
    for i in range(len(V)):
        if colors[i] == 1 or colors[i] == 2:
            newV.append((V[i], colors[i]-1))
            vertex_colors[V[i]].append(colors[i]-1)
        if colors[i] >= 3:
            newV.append((V[i], 0))
            newV.append((V[i], 1))
            ##block_ordering_graph[(V[i], 0)].append(((V[i], 1), 1)) - закомментировать это?
            ##block_ordering_graph[(V[i], 1)].append(((V[i], 0), 1))
            block_ordering_graph[(V[i], 0)].append(((V[i], 1), 1))
            block_ordering_graph[(V[i], 1)].append(((V[i], 0), 1))
            vertex_colors[V[i]].append(0)
            vertex_colors[V[i]].append(1)

    for t in newV:
        x = t[0]
        if not was[x] and len(F[x]) == 1:
            tmp = dfs(x)
            a, b = t, (tmp, vertex_colors[tmp][0])
            block_ordering_graph[a].append((b, 1))
            block_ordering_graph[b].append((a, 1))

    for x in itertools.chain(A, B):
        s, t = -x[0], x[-1]
        if s == t:
            continue
        if s in vertex_colors and t in vertex_colors:
            available_colors = set(vertex_colors[s]).intersection(set(vertex_colors[t]))
            if available_colors:
                for c in available_colors:
                    vs, vt = (s, c), (t, c)
                    block_ordering_graph[vs].append((vt, 0))
                    block_ordering_graph[vt].append((vs, 0))

    return newV, vertex_colors, block_ordering_graph


def join_beta_edges(block_ordering_graph):
    removed = []
    new_graph = defaultdict(list)
    was = defaultdict(int)
    colors = defaultdict(int)
    prev = {}
    def dfs(v, color, p=-1):
        prev[v] = p
        was[v] = 1
        colors[v] = color
        for t, tmp in block_ordering_graph[v]:
            if not was[t]:
                if t[1] == v[1]:
                    return  dfs(t, color, v)
                else:
                    return dfs(t, color, -1)
        return v

    def one_sided(v):
        #count one sided edges
        res = 0
        for tmp, c in block_ordering_graph[v]:
            if tmp[1] == v[1]:
                res += 1
        return res

    color = 1
    for v in block_ordering_graph:
        if not was[v] and one_sided(v) <= 1:
            prev[v] = dfs(v, color)
            color += 1

    pres = defaultdict(int)
    for v in block_ordering_graph:
        if pres[colors[v]] == 3:
            continue
        if v[1] == 0:
            if pres[colors[v]] != 1:
                pres[colors[v]] += 1
        else:
            if pres[colors[v]] != 2:
                pres[colors[v]] += 2

    for v in block_ordering_graph:
        if pres[colors[v]] == 3:
            for t, c in block_ordering_graph[v]:
                if v[1] != t[1]:
                    new_graph[v].append((t, c))
                else:
                    if c == 1:
                        removed.append((v, t))
            if one_sided(v) == 1 and prev[v] != -1:
                cur = prev[v]
                while prev[cur] != -1:
                    cur = prev[cur]
                new_graph[v].append((cur, 0))
                new_graph[cur].append((v, 0))

        else:
            for t, c in block_ordering_graph[v]:
                new_graph[v].append((t, c))

    return removed, new_graph


def construct_edge_matching_graph(BOG):
    V = set()
    for v in BOG:
        for t, c in BOG[v]:
            if t[1] != v[1]:
                V.add((min(v, t), max(v, t), c))

    EMG = defaultdict(list)

    for v in V:
        s1, s2, c = v
        for another_s1, c1 in BOG[s1]:
            if another_s1 != s2:
                for another_s2, c2 in BOG[another_s1]:
                    if another_s2 != s1 and c1 == 0:
                        v2 = (min(another_s2, another_s1), max(another_s2, another_s1), c2)
                        color = another_s1[1]
                        if v2 in V:
                            EMG[v].append((v2, color))

        for another_s1, c1 in BOG[s2]:
            if another_s1 != s1:
                for another_s2, c2 in BOG[another_s1]:
                    if another_s2 != s2 and c1 == 0:
                        v2 = (min(another_s2, another_s1), max(another_s2, another_s1), c2)
                        color = another_s1[1]
                        if v2 in V:
                            EMG[v].append((v2, color))

    return V, EMG
    

def get_score(FBG, BOG, EMG, beta, A, B):
    was = defaultdict(int)
    def dfs_cycles(v, p=-1):
        was[v] = 1
        for x in FBG[v]:
            if not was[x]:
                return dfs_cycles(x, v)
            else:
                if x != p:
                    return 1
        return 0

    gamma = 0
    for v in FBG:
        if not was[v]:
            gamma += dfs_cycles(v)

    lb = len(beta)/2

    k = 0
    la = 0
    for v in BOG:
        for t, c in BOG[v]:
            if v[1] != t[1]:
                k += 1
            elif c == 1:
                la += 1
    k /= 4
    la /= 2

    was.clear()
    def dfs_one_sided(v, c):
        was[v] = 1
        for t, col in BOG[v]:
            if t[1] != c:
                return 0
            if not was[t]:
                dfs_one_sided(t, c)
        return 1

    w = 0
    for v in BOG:
        if not was[v]:
            w += dfs_one_sided(v, v[1])

    print(len(A), len(B))
    print(gamma, k, la, lb, w)
    print(min((gamma + k + la + lb - w)/(len(A) + len(B)), 1))


def edge_matching_algorithm(VE, EMG, n):
    base_a = None
    base_b = None
    for s1, s2, c in VE:
        if s1[0] == s2[0] == 0:
            base_a = (s1, s2, c)
        if abs(s1[0]) == abs(s2[0]) == n:
            base_b = (s1, s2, c)

    if base_a and base_b:
        EMG[base_a].append((base_b, 0))
        EMG[base_a].append((base_b, 1))
        EMG[base_b].append((base_a, 1))
        EMG[base_b].append((base_a, 0))

    # rank = defaultdict(int)
    # parent = {}
    # def make_set(v):
    #     parent[v] = v
    #     rank[v] = 0
    #
    # def find_set(v):
    #     if v == parent[v]:
    #         return v
    #     parent[v] = find_set(parent[v])
    #     return parent[v]
    #
    # def union_sets(a, b):
    #     ta = find_set(a)
    #     tb = find_set(b)
    #     if ta != tb:
    #         if rank[ta] < rank[tb]:
    #             t = ta
    #             ta = tb
    #             tb = t
    #         parent[tb] = ta
    #         if rank[ta] == rank[tb]:
    #             rank[ta] += 1
    path0 = defaultdict(list)
    path1 = defaultdict(list)
    for x in EMG.keys():
        #две копии вершины - для черных путей и для белых
        path0[x] = [(x, -1)]
        path1[x] = [(x, -1)]
        for t, c in EMG[x]:
            if c == 1:
                path1[x].append((t, c))
            else:
                path0[x].append((t, c))


    def valid_matching(a, b):
        if a == b:
            return False
        pab = path1[a]
        pbb = path1[b]
        paw = path0[a]
        pbw = path0[b]
        if pab[-1][0] == b or paw[-1][0] == b:
            return False
        if pab and pbb and paw and pbw:
            return True
        else:
            return False

    def join_matching(a, b):
        pab = path1[a]
        pbb = path1[b]

        paw = path0[a]
        pbw = path0[b]

        eab = pab[-1][0]
        ebb = pbb[-1][0]

        path1[eab] += [(b, 3)]
        path1[eab] += pbb.copy()[1:]

        path1[ebb] += [(a, 3)]
        path1[ebb] += pab.copy()[1:]

        path1[a] = []
        path1[b] = []

        eaw = paw[-1][0]
        ebw = pbw[-1][0]

        path0[eaw] += [(b, 3)]
        path0[eaw] += pbw.copy()[1:]

        path0[ebw] += [(a, 3)]
        path0[ebw] += paw.copy()[1:]

        path0[a] = []
        path0[b] = []


    matching = set()
    unused = set(EMG.keys()).copy()
    while len(matching)+1 < len(EMG.keys())/2:
        f = False
        #print(unused)
        r1 = 0
        r0 = 0
        for x in path1.values():
            if x:
                r1 += 1

        for x in path0.values():
            if x:
                r0 += 1
        for i, a in enumerate(list(unused)):
            for j, b in enumerate(list(unused)[i+1:]):
                if valid_matching(a, b):
                    matching.add((a, b))
                    join_matching(a, b)
                    unused.remove(a)
                    unused.remove(b)
                    f = True
                    break
            if f:
                break

    #if len(unused):
        #matching.add((list(unused)[0], list(unused)[1]))

    tot0 = []
    tot1 = []
    for x in path0.values():
        if x:
            tot0 += [y[0][0] for y in x]
    for x in path1.values():
        if x:
            tot1 = tot1 + [y[0][1] for y in x]



def find_distance(A, B):
    n = A[-1][0]
    print("constructing fragment breakpoint graph")
    V, colors, fbg = construct_fragmented_breakpoint_graph(A, B, n)
    print("constructing block orientation graph")
    newV, vertex_colors, BOG = construct_block_ordering_graph(V, colors, fbg, A, B)
    print("removing beta one sided edges")
    removed, BOG_filtered = join_beta_edges(BOG)
    print("constructing edge matching graph")
    VE, EMG = construct_edge_matching_graph(BOG_filtered)
    #print(VE)
    #print(EMG[((2212, 0), (2212, 1), 1)])
    print("solving edge matching problem")
    ####
    edge_matching_algorithm(VE, EMG, n)


    print("counting_score")
    get_score(fbg, BOG_filtered, EMG, removed, A, B)



if __name__ == "__main__":
    if len(sys.argv) > 1:
        filename = sys.argv[1]
    else:
        filename = "output.txt"
    with open(filename) as inp:
        lines = inp.readlines()
    n, m = [int(x) for x in lines[0].split()]
    A = []
    B = []
    for i in range(1, n+1):
        A.append([int(x) for x in lines[i].split()])
    for j in range(n+1, n+m+1):
        B.append([int(x) for x in lines[j].split()])
    ta = []
    for x in A[1:-1]:
        for y in x:
            ta.append(y)

    tb = []
    for x in B[1:-1]:
        for y in x:
            tb.append(y)

    ta = [A[0]] + [ta] + [A[-1]]
    tb = [B[0]] + [tb] + [B[-1]]
    find_distance(A, B)
