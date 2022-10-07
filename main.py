import random
class Graph:
    n = 0
    m = 0
    d = 0
    edges = []

    def init(self, n, m, d):
        self.n = n
        self.m = m
        self.d = d

    def getAdjacentEdges(self, v):
        edgeList = []
        for e in self.edges:
            if e[0] == v or e[1] == v: edgeList.append(e)
        return edgeList

    def readGraph(self, filename):
        with open(filename) as f:
            lines = f.readlines()
            for line in lines:
                split = line.split()
                if split[0] == "c":  continue
                if split[0] == "graph":
                    self.init(int(split[1]), int(split[2]), int(split[3]))
                    continue
                self.edges.append([int(split[0]), int(split[1]), int(split[2]), int(split[3])])

    def generateRandomGraph(self, n, p, d):
        for v in range(1,n+1):
            for u in range(v+1, n+1):
                for cv in range(1,d+1):
                    for cu in range(1,d+1):
                        if random.random() < p:
                            self.edges.append([v,u,cv,cu])
        self.init(n, len(self.edges), d)

    def generateCompleteBipartiteGraph(self, n1, n2, d):
        for v in range(1,n1+1):
            for u in range(n1+1,n1 + n2 + 1):
                for cv in range(1,d+1):
                    for cu in range(1,d+1):
                        self.edges.append([v,u,cv,cu])
        self.init(n1+n2,len(self.edges),d)

def allocateVar(map, string):
    number = len(map) + 1
    map[string] = number


def getVCString(v, color):
    return "vertex %x has color %x" % (v, color)


def getEdgeString(e):
    return "edge " + repr(e[0]) + " and " + repr(e[1]) + " with color " + repr(e[2]) + " and " + repr(e[3])


def getTutteVariableString(v):
    return "vertex %d is in Tutte Set" % v


def getRestEdgeString(e):
    return "edge %d %d %d %d is in the subgraph of V-S" % (e[0], e[1], e[2], e[3])


def getConnectedComponentString(v,i):
    return "vertex %d is in component %i" % (v,i)


def getOddComponentString(i):
    return "component %d is an odd component" % i


def generatePMFormula(graph, formulaPath):
    varMap = {}
    for e in graph.edges:
        allocateVar(varMap, getEdgeString(e))
    for i in range(1, graph.n + 1):
        for j in range(1, graph.d + 1):
            allocateVar(varMap, getVCString(i, j))
    print(varMap)

    with open(formulaPath, 'w+') as f:
        # perfect matching edges
        f.write("c color constraints\n")
        for e in graph.edges:
            f.write("im %d -> ( %d & %d ) \n" % (
                varMap[getEdgeString(e)], varMap[getVCString(e[0], e[2])], varMap[getVCString(e[1], e[3])]))
        # exact-one edges
        f.write("c exact-one edges for PM\n")
        for i in range(1, graph.n + 1):
            edgeList = graph.getAdjacentEdges(i)
            if len(edgeList) > 0:
                f.write("eo ")
                for e in edgeList:
                    f.write(repr(varMap[getEdgeString(e)]) + " ")
                f.write("\n")
            else:
                f.write('false\n')
        # exact-one for ad-hoc color of each vertex
        f.write("c exact-one for ad-hoc color of each vertex\n")
        for i in range(1, graph.n + 1):
            f.write("eo ")
            for j in range(1, graph.d + 1):
                f.write(repr(varMap[getVCString(i, j)]) + " ")
            f.write('\n')
        # symmetric function for vertex coloring
        f.write("co ")
        for i in range(1, graph.n + 1):
            f.write(repr(varMap[getVCString(i, 1)]) + " ")
        f.write('\n')
    return len(varMap)



def generateNEPMFormula(graph, formulaPath):
    varMap = {}
    for i in range(1, graph.n + 1):
        allocateVar(varMap,getTutteVariableString(i))
    for i in range(1, graph.n + 1):
        allocateVar(varMap, getOddComponentString(i))
    for i in range(1, graph.n + 1):
        for j in range(1,graph.n + 1):
            allocateVar(varMap, getConnectedComponentString(i,j))
    for e in graph.edges:
        allocateVar(varMap, getEdgeString(e))
        allocateVar(varMap, getRestEdgeString(e))
    for i in range(1, graph.n + 1):
        for j in range(1, graph.d + 1):
            allocateVar(varMap, getVCString(i, j))
    print(varMap)
    with open(formulaPath, 'w+') as f:
        # exact-one for ad-hoc color of each vertex
        f.write("c exact-one for ad-hoc color of each vertex\n")
        for i in range(1, graph.n + 1):
            f.write("eo ")
            for j in range(1, graph.d + 1):
                f.write(repr(varMap[getVCString(i, j)]) + " ")
            f.write('\n')
        for e in graph.edges:
            f.write("le %d <-> ( ! %d & ! %d ) & ( %d & %d ) \n" % (varMap[getRestEdgeString(e)], varMap[getTutteVariableString(e[0])], varMap[getTutteVariableString(e[1])], varMap[getVCString(e[0], e[2])],
                                                               varMap[getVCString(e[1],e[3])]))
        for e in graph.edges:
            for i in range(1,graph.n+1):
                f.write("cc %d -> ( %d = %d )\n" % (varMap[getRestEdgeString(e)], varMap[getConnectedComponentString(e[0],i)], varMap[getConnectedComponentString(e[1],i)] ))

        for i in range(1, graph.n+1):
            f.write("x %d " % varMap[getOddComponentString(i)])
            for j in range(1, graph.n  + 1 ):
                f.write("%d " % varMap[getConnectedComponentString(j,i)])
            f.write("\n")

        for i in range(1, graph.n+1):
            f.write('eo ')
            f.write('%d ' % varMap[getTutteVariableString(i)])
            for j in range(1, graph.n + 1 ):
                f.write("%d " % varMap[getConnectedComponentString(i,j)])
            f.write("\n")

        f.write('card ')
        for i in range(1, graph.n+1):
            f.write("%d -%d " % (varMap[getOddComponentString(i)], varMap[getTutteVariableString(i)]))
        f.write(">= 1 ;\n")
        return len(varMap)


def PBEncoding(formulaPath, PBPath, nv):
    with open(formulaPath) as f:
        lines = f.readlines()
        with open(PBPath, 'w+') as g:
            g.write("* #variable= 1 #constraint= 1\n")
            for line in lines:
                split = line.split()
                if split[0] == 'c': continue
                if split[0] == 'eo':
                    for k in range(1, len(split)):
                        g.write("+1 x%d " % int(split[k]))
                    g.write(" = 1 ;\n")
                if split[0] == 'co':
                    for k in range(1, len(split)):
                        g.write("+1 x%d " % int(split[k]))
                    g.write(" >= %d ;\n" % (graph.n / 2) )
                if split[0] == 'im':
                    g.write("-1 x%d +1 x%d >= 0 ; \n" % (int(split[1]), int(split[4])))
                    g.write("-1 x%d +1 x%d >= 0 ; \n" % (int(split[1]), int(split[6])))
                if split[0] == 'false':
                    g.write("+1 x1 = 2 ;\n")
                if split[0] == 'x':
                    g.write("* xor ")
                    for k in range(1, len(split)):
                        g.write("x%d " % int(split[k]))
                    g.write("0 \n")
                if split[0] == 'card':
                    for k in range(1, len(split)-3):
                        if int(split[k]) > 0:
                            g.write("+1 x%s " % (split[k]))
                        else:
                            g.write("-1 x%d " % (-int(split[k])))
                    g.write("%s %s %s\n" % (split[-3],split[-2],split[-1]))
                if split[0] == 'cc':
                    nv += 1
                    g.write("-1 x%s +1 x%d >= 0\n" % (split[1], nv) )
                    g.write("* xor x%s x%s x%d 1\n" % (split[4], split[6], nv))
                if split[0] == 'le':
                    g.write("+1 x%s +1 x%s +1 x%s -1 x%s -1 x%s >= -1 ;\n" % (split[1],split[5],split[8],split[12],split[14]))
                    g.write("-4 x%s -1 x%s -1 x%s +1 x%s +1 x%s >= -2 ;\n" % (split[1],split[5],split[8],split[12],split[14]))
    print("nv %d " % (nv))

# Press the green button in the gutter to run the script.
if __name__ == '__main__':
    graph = Graph()
    #graph.readGraph('graph.txt')
    #graph.readGraph('bipartite.txt')
    #graph.generateRandomGraph(20,0.001,3)
    graph.generateCompleteBipartiteGraph(20,22,1)

    pmnv = generatePMFormula(graph, "formula.txt")
    nepmnv = generateNEPMFormula(graph, "nepmformula.txt")
    PBEncoding("formula.txt", "pmpb.txt", pmnv)
    PBEncoding("nepmformula.txt", "nepmpb.txt", nepmnv)
    print(graph.edges)
