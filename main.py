import random
import os
import math
import argparse

class Graph:
    def __init__(self):
        self.n = 0
        self.m = 0
        self.d = 0
        self.edges = []

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

    def generateRandomGraph(self, n, d, p):
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

    def generateBicoloredCompleteGraph(self,n,d):
        for v in range(1, n + 1):
            for u in range(v+1, n + 1):
                for cv in range(1, d + 1):
                    for cu in range(1, d + 1):
                        self.edges.append([v,u,cv,cu])
        self.init(n,n*(n-1)/2*d*d, d)

    def generateCompleteGraph(self,n,d):
        for v in range(1, n + 1):
            for u in range(v+1, n + 1):
                for c in range(1, d + 1):
                        self.edges.append([v,u,c,c])
        self.init(n,n*(n-1)/2*d, d)

    def generateCycle(self, n):
        for v in range(n):
            if v % 2 == 0:
                self.edges.append([v+1 , (v+1) % n + 1, 1, 1])
            else:
                self.edges.append([v+1 , (v+1) % n + 1, 2, 2])
        self.init(n,n,2)

def allocateVar(mapping, string):
    if string in mapping:
        return mapping[string]
    else:
        number = len(mapping) + 1
        mapping[string] = number
        return number


def getVCString(v, color):
    return "vertex %x has color %x" % (v, color)


def getPMEdgeString(e):
    return "edge " + repr(e[0]) + " and " + repr(e[1]) + " with color " + repr(e[2]) + " and " + repr(e[3]) + " is in PM"

def getEdgeFromString(s):
    split = s.split()
    return [int(split[1]), int(split[3]), int(split[6]), int(split[8])]

def getEdgeString(e):
    return "edge " + repr(e[0]) + " and " + repr(e[1]) + " with color " + repr(e[2]) + " and " + repr(e[3]) + " is in the graph"

def getTutteVariableString(v):
    return "vertex %d is in Tutte Set" % v


def getRestEdgeString(e):
    return "edge %d %d %d %d is in the subgraph of V-S" % (e[0], e[1], e[2], e[3])

def getLearnedEdgeString(e,count):
    return "edge %d %d %d %d is needed in round %d" % (e[0], e[1], e[2], e[3], count)

def getConnectedComponentString(v,i):
    return "vertex %d is in component %i" % (v,i)


def getOddComponentString(i):
    return "component %d is an odd component" % i

def getExtraVariableString(index):
    return "an auxiliary variable with index %d" % index

def generateGraphDiscoveryFormula(graph, PMFormulaPath, NEPMFormulaPath, PBXORPath):
    varMap = {}
    for e in graph.edges:
        allocateVar(varMap,getEdgeString(e))
    generatePMFormula(graph,PMFormulaPath,varMap)
    generateNEPMFormula(graph,NEPMFormulaPath,varMap)
    constraintList = ["* #variable= 1 #constraint= 1\n"]
    PBEncoding(PMFormulaPath,varMap, constraintList)
    PBEncoding(NEPMFormulaPath, varMap, constraintList)
    constraintList[0] = "* #variable= %d #constraint= %d\n" % (len(varMap),len(constraintList) -1 )
    with open(PBXORPath,'w+') as f:
        for constraint in constraintList:
            f.write(constraint)

def generatePMFormula(graph, formulaPath, varMap, state):
    for e in graph.edges:
        allocateVar(varMap, getPMEdgeString(e))
    for i in range(1, graph.n + 1):
        for j in range(1, graph.d + 1):
            allocateVar(varMap, getVCString(i, j))

    with open(formulaPath, 'w+') as f:
        # perfect matching edges
        f.write("c color constraints\n")
        #for e in graph.edges:
        #    f.write("imply %d -> %d\n" % (varMap[getPMEdgeString(e)], varMap[getEdgeString(e)]))
        for e in graph.edges:
            f.write("im %d -> ( %d & %d ) \n" % (
                varMap[getPMEdgeString(e)], varMap[getVCString(e[0], e[2])], varMap[getVCString(e[1], e[3])]))
        # exact-one edges
        f.write("c exact-one edges for PM\n")
        for i in range(1, graph.n + 1):
            edgeList = graph.getAdjacentEdges(i)
            if len(edgeList) > 0:
                f.write("eo ")
                for e in edgeList:
                    f.write(repr(varMap[getPMEdgeString(e)]) + " ")
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
        if state == "GHZ":
        #NAE(vc(1,r),vc(2,r),...) for GHZ states
            for j in range(1, graph.d + 1):
                f.write("nae ")
                for i in range(1,graph.n+1):
                    f.write("%d " % (varMap[getVCString(i,j)]))
                f.write('\n')
        elif state == "W": # todo: think of the negation of exact-one
            f.write("eo ")
            for i in range(1,graph.n+1):
                f.write("%d " % varMap[getVCString(i,1)])
            f.write()
    return len(varMap)

def generateNEPMFormula(graph, formulaPath, varMap, state):
    for i in range(1, graph.n + 1):
        allocateVar(varMap,getTutteVariableString(i))
    for i in range(1, graph.n + 1):
        allocateVar(varMap, getOddComponentString(i))
    for i in range(1, graph.n + 1):
        for j in range(1,graph.n + 1):
            allocateVar(varMap, getConnectedComponentString(i,j))
    for e in graph.edges:
        allocateVar(varMap, getRestEdgeString(e))
    for i in range(1, graph.n + 1):
        for j in range(1, graph.d + 1):
            allocateVar(varMap, getVCString(i, j))
    with open(formulaPath, 'w+') as f:
        # exact-one for ad-hoc color of each vertex
        f.write("c exact-one for ad-hoc color of each vertex\n")
        #for e in graph.edges:
        #    f.write("imply %d -> %d\n" % (varMap[getRestEdgeString(e)], varMap[getEdgeString(e)]))
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

        # todo: AE(vc(1,r),vc(2,r),...) for GHZ states
        if state == "GHZ":
            for j in range(1, graph.d + 1):
                f.write("ae ") # ae = all-equal
                for i in range(1, graph.n + 1):
                    f.write("%d " % (varMap[getVCString(i, j)]))
                f.write('\n')
            return len(varMap)
        elif state == "W":
            f.write("eo ")
            for i in range(1,graph.n+1):
                f.write("%d " % varMap[getVCString(i,1)])
            f.write('\n')


def PBEncoding(formulaPath, varMap, constraintList):
    with open(formulaPath) as f:
        lines = f.readlines()
        for line in lines:
            split = line.split()
            if split[0] == 'c': continue
            if split[0] == 'eo':
                string = ""
                for k in range(1, len(split)):
                    string += ("+1 x%d " % int(split[k]))
                string += " = 1 ;\n"
                constraintList.append(string)
            if split[0] == 'co':
                string = ""
                for k in range(1, len(split)):
                    string += ("+1 x%d " % int(split[k]))
                string += (" >= %d ;\n" % (graph.n / 2) )
                constraintList.append(string)
            if split[0] == 'im':
                constraintList.append("-1 x%d +1 x%d >= 0 ; \n" % (int(split[1]), int(split[4])))
                constraintList.append("-1 x%d +1 x%d >= 0 ; \n" % (int(split[1]), int(split[6])))
            if split[0] == 'imply':
                constraintList.append("-1 x%d +1 x%d >= 0 ; \n" % (int(split[1]), int(split[3])))
            if split[0] == 'false':
                constraintList.append("+1 x1 = 2 ;\n")
            if split[0] == 'x':
                string = "* xor "
                for k in range(1, len(split)):
                    string +=("x%d " % int(split[k]))
                string += "0 \n"
                constraintList.append(string)
            if split[0] == 'card':
                string = ""
                for k in range(1, len(split)-3):
                    if int(split[k]) > 0:
                        string += ("+1 x%s " % (split[k]))
                    else:
                        string += ("-1 x%d " % (-int(split[k])))
                string += ("%s %s %s\n" % (split[-3],split[-2],split[-1]))
                constraintList.append(string)
            if split[0] == 'cc':
                index = allocateVar(varMap, getExtraVariableString(len(varMap)))
                constraintList.append("-1 x%s +1 x%d >= 0\n" % (split[1], index) )
                constraintList.append("* xor x%s x%s x%d 1\n" % (split[4], split[6], index))
            if split[0] == 'le':
                constraintList.append("+1 x%s +1 x%s +1 x%s -1 x%s -1 x%s >= -1 ;\n" % (split[1],split[5],split[8],split[12],split[14]))
                constraintList.append("-4 x%s -1 x%s -1 x%s +1 x%s +1 x%s >= -2 ;\n" % (split[1],split[5],split[8],split[12],split[14]))
            if split[0] == 'nae':
                stringneg = ""
                for k in range(1,len(split)):
                    stringneg += ("-1 x%s " % split[k] )
                constraintList.append(stringneg + ">= " + repr(-len(split)+2) + " ;\n")
            if split[0] == 'ae':
                for k in range(1,len(split)-1):
                    constraintList.append("* xor x%s x%s 0\n" % (split[k],split[k+1]))
                        
                
def checkNEPM(graph, state, NEPMFormulaPath="nepmformula.txt", PBXORNEPMFormulaPath="pbxornepmformula.txt"): # check the nepm comdition for all legal states. if the extended graph with unassigned edges are true has no illegal PM, return true. otherwise return false.
    varMap = {}
#    if not checkLearnedConflicts(graph,learnedConstraints): return False
#    for e in graph.edges:
#        allocateVar(varMap,getEdgeString(e))
    generateNEPMFormula(graph,NEPMFormulaPath,varMap,state)
    constraintList = ["* #variable= 1 #constraint= 1\n"]
    PBEncoding(NEPMFormulaPath,varMap, constraintList)
    constraintList[0] = "* #variable= %d #constraint= %d\n" % (len(varMap),len(constraintList) -1 )
    with open(PBXORNEPMFormulaPath,'w+') as f:
        for constraint in constraintList:
            f.write(constraint)
    cmd = '../../linpb/build/linpb %s --print-sol=1 > nepmres.txt' % PBXORNEPMFormulaPath
    os.system(cmd)
    # todo: call libpb. if SAT, return False. otherwise return true
    return readLinpbRes("nepmres.txt", "NEPM", graph, varMap)

def readPMfromRes(split, graph):
    # split is the split of vline
    pm = set()
    pmVars = []
    for i in range(min(len(graph.edges), len(split))):
        if split[i][0] == 'x':
            edgeStr = getEdgeString(graph.edges[i])
            pm.add(edgeStr) 
    #todo: make the edges as unique id. Then use set inclusion for graphs to see whether the PM is there.
    print('learned PM: '+repr(pm))
    return pm

def readColoringfromRes(vlineSplit, graph, varMap):
    coloring = {}
    positiveVarSet = set()
    for s in vlineSplit:
        if s[0] == 'x':
            positiveVarSet.add(int(s[1:]))
    for i in range(1, graph.n+1):
        for c in range(1, graph.d+1):
            var = varMap[getVCString(i,c)]
            if var in positiveVarSet:
                coloring[i] = c
                break
    if len(coloring) != graph.n: 
        print("incomplete coloring!")
        exit(0)
    return coloring

def readLinpbRes(resFile,problemType,graph, varMap): # problemType = {'PM','NEPM'}
    with open(resFile,'r') as f:
        lines = f.readlines()
        for line in lines:
            split = line.split()
            if len(split) == 0: continue
            if split[0] == 's':
                if split[1] == 'UNSATISFIABLE': return True
                elif split[1] == 'SATISFIABLE': 
                    pass
            if split[0] == 'v':
                #todo: retract the PM and add it to the forbidden list
                if problemType == "PM":
                    pm = readPMfromRes(split[1:],graph)
                    print("illegal PM")
                    print(pm)
                if problemType == "NEPM": 
                    eoList = {}
                    for i in range(1,graph.n+1):
                        eoList[i] = []
                    coloring = readColoringfromRes(split[1:], graph, varMap)
                    print("no PM for coloring ")
                    print(coloring)
        return False
        
def checkPM(graph, state, PMFormulaPath="pmformula.txt", PBXORPMFormulaPath="pbxorpmformula.txt"): # if the extended graph with unassigned edges are false has no proof of non-existence of PM, return true. Otherwise return true
    varMap = {}
 #   if not checkLearnedConflicts(graph,learnedConstraints): return False
 #   for e in graph.edges:
 #       allocateVar(varMap, getEdgeString(e))
    generatePMFormula(graph, PMFormulaPath, varMap, state)
    constraintList = ["* #variable= 1 #constraint= 1\n"]
    PBEncoding(PMFormulaPath, varMap, constraintList)
    constraintList[0] = "* #variable= %d #constraint= %d\n" % (len(varMap), len(constraintList) - 1)
    with open(PBXORPMFormulaPath, 'w+') as f:
        for constraint in constraintList:
            f.write(constraint)
    cmd = '../../linpb/build/linpb --print-sol=1 %s > pmres.txt' % PBXORPMFormulaPath
    os.system(cmd)
    # todo: call libpb. if SAT, return False. otherwise return true
    return readLinpbRes("pmres.txt", "PM", graph, varMap)    

def makeStateConstraints(stateInputStyle, state):
    pass

def identification(graph, stateInputStyle='name', state='GHZ'):
    # stateInputStyle is in {'name', 'enumerate', 'constraint'}
    # for 'name', state is in {'GHZ','W'}
    # for 'enumerate', state is the file name of the list of legal states, e.g., 1,1,1,1 2,2,2,2 3,3,3,3
    # for 'constraint', state is the constraint that defines the legal states, e.g., ae 1 2 3 4 (GHZ state)
    stateConstraints = makeStateConstraints(stateInputStyle, state)
    pmFlag = checkPM(graph, state)
    if pmFlag == False: return False
    else: 
        print('no illegal PMs')
    print('checking for absense of legal colorings')
    nepmFlag = checkNEPM(graph, state)
    return nepmFlag 
 
if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--state',type=str, help='GHZ,W')
    parser.add_argument('--graphFile',type=str,help='the graph file')
    args = parser.parse_args()
    graph = Graph()
    #graph.readGraph(graphFile)
    for n in range(10,20,2):
        graph.generateCycle(n)
        #graph.generateRandomGraph(n,2, 1/math.sqrt(n))
        flag = identification(graph, stateInputStyle='name', state='GHZ')
        print("n = "+ repr(n) + " result = " + repr(flag))
