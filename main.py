# This is a sample Python script.

# Press ⌃R to execute it or replace it with your code.
# Press Double ⇧ to search everywhere for classes, files, tool windows, actions, and settings.

class Graph:
    n = 0
    m = 0
    d = 0
    edges = []
    def init(self,n,m,d):
        self.n = n
        self.m = m
        self.d = d

def readGraph(filename):
    graph = Graph()
    with open(filename) as f:
        lines = f.readlines()
        for line in lines:
            split = line.split()
            if split[0] == "c":  continue
            if split[0] == "graph":
                graph.init(int(split[1]), int(split[2]), int(split[3]))








def print_hi(name):
    # Use a breakpoint in the code line below to debug your script.
    print(f'Hi, {name}')  # Press ⌘F8 to toggle the breakpoint.


# Press the green button in the gutter to run the script.
if __name__ == '__main__':
    print_hi('PyCharm')

# See PyCharm help at https://www.jetbrains.com/help/pycharm/
