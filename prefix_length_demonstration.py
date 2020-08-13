import ipaddress

###DEFINED FUNCTIONS AND CLASSES
class Tree:
    def __init__(self):
        self.left = None
        self.right = None
        self.father = None
        self.len = None #corresponding to the len that the node is representing
        self.index = None #corresponding to the index of the hash table that the node is representing

    def construct(self, left, midle, right, hash_table):
        #print(left,"   ",midle,"   ",right)
        self.len = len(hash_table[midle][0])
        self.index = midle
        if midle - 1 > left:#It means there are hashes between the midle and left hashes
            #creates a node correspondent to the hash table in the midle of the previous two hashes
            self.left = Tree()
            self.left.father = self
            #print("left\n")
            self.left.construct(left,  left + int((midle-left)/2), midle, hash_table)
        if midle + 1 < right:#It means there are hashes between the midle and left hashes
            #creates a node correspondent to the hash table in the midle of the previous two hashes
            self.right = Tree()
            self.right.father = self
            #print("right\n")
            self.right.construct(midle , midle + int((right-midle)/2), right, hash_table)

    def searchchildren(self, len):#Given the lenght of a node.
        node = self
        # navigate the tree
        while 1:#Find the node correspondant to the given index (correspondent to the hash table of the same lenght)
            #print(node.len)
            if len == node.len:
                break
            else:
                if len < node.len:
                    node = node.left
                else:
                    node = node.right
        #print(node.len)
        #Return the hashes tables that have it correspondent nodes at the right of the found node
        children = []
        if node.right:
            children.append(node.right.index)##
            self.returnchildren(node.right, children)
        #print(children)
        return children

    def returnchildren(self, node, children):
        #Return all the children at the right##
        #if not node.right and not node.left:#Just return the final nodes
        #    children.append(node.len)
        #else:#In a recursive way it will find the final nodes
        if node.left:
            children.append(node.left.index)##
            self.returnchildren(node.left, children)
        if node.right:
            children.append(node.right.index)##
            self.returnchildren(node.right, children)

    def addmarkers(self, hash_table, n):
        for i in range(0, n):#for each hash table (node)
            children = self.searchchildren(len(hash_table[i][0]))#find the final nodes at the right of this node (childrens)
            #In the current node we will introduce the hashes of the childresn as markers
            #print(i,"-----",children)
            for j in children:
                for k in hash_table[j]:
                    if k[:len(hash_table[i][0])] in hash_table[i]:
                        hash_table[i].remove(k[:len(hash_table[i][0])])
                        hash_table[i].append(k[:len(hash_table[i][0])]+"p")#The p indicates that it is a marker and a prefix.
                    else:
                        hash_table[i].append(k[:len(hash_table[i][0])]+"m")#The m indicates that it is just a marker

    def addBMP(self, hash_table, n):
        for i in range(n-1,0,-1):#for all the hash tables
            #for each hash table it will be introduce the bmp value to the markers, this value corresponds at the backtrack prefix in case it is needed.
            for j in hash_table[i]:
                if j[len(hash_table[i][0]):] == "m":
                    k = i-1
                    found = None
                    while found != True:
                        for l in hash_table[k]:
                            if l[:len(hash_table[k][0])] == j[:len(hash_table[k][0])] and l[len(hash_table[k][0]):] != "m":
                                hash_table[i].append(l[:len(hash_table[k][0])]+"bmp")#Introduce the bmp as the prefix value plus "bmp" indicating it is a bmp.
                                found = True
                                break
                        k += -1
                        if k == -1: #just for security (avoid inifinite loop)
                            break
    def lookup(self, hash_table, ip):
        node = self
        while 1:
            if ip[:node.len] in list(map(lambda i:i[:node.len],hash_table[node.index])):#if the ip input sliced is in this hashtable
                position=list(map(lambda i: i[:node.len], hash_table[node.index])).index(ip[:node.len])
                if hash_table[node.index][position][-1:] == "m" or  hash_table[node.index][position][-1:] == "p":#ask if it is a marker, in case it is, point to the right in case it is not, the prefix lenght is returned
                    node = node.right
                else:
                    return node.index
            else:#if the ip input is not found in the current hash table point to the left
                if node.left:
                    node = node.left
                else:#in case the hash is represented by a final node, we need to backtrak
                    #####Backtrack#######
                    node = node.father
                    while 1:
                        if "bmp" in list(map(lambda i:i[-3:],hash_table[node.index])):#cheking the father node has a bmp
                            position = list(map(lambda i:i[-3:],hash_table[node.index])).index("bmp")
                            len_bmp = len(hash_table[node.index][position][:-3])#taking the len correspondent to the index of the hash table that has the bactracked prefix
                            if hash_table[node.index][position][:len_bmp] == ip[:len_bmp]:
                                return self.search_index_len_bmp(len_bmp)
                            else:
                                node=node.father
    def search_index_len_bmp(self ,len_bmp):
        node = self
        while 1:#Find the node correspondant to the given index (correspondent to the hash table of the same lenght)
            #print(node.len)
            if len_bmp == node.len:
                break
            else:
                if len_bmp < node.len:
                    node = node.left
                else:
                    node = node.right
        return node.index
##################################################MAIN CODE ###################################################################
# IP lookup parameters
IP = 0
SUBNET = 1
DPID = 2

switch = {}
#####Prove Switches#############
switch["194.0.0.254"] = ["194.0.0.254", "0", "2"]
switch["137.0.0.254"] = ["137.0.0.254", "1", "2"]
switch["10.0.0.254"] = ["10.0.0.254", "2", "6"]
switch["166.0.0.254"] = ["166.0.0.254", "3", "3"]
switch["254.0.0.254"] = ["254.0.0.254", "3", "3"]
switch["128.0.0.254"] = ["128.0.0.254", "4", "5"]
switch["232.0.0.254"] = ["232.0.0.254", "5", "7"]
switch["229.0.0.254"] = ["229.0.0.254", "6", "8"]
switch["150.0.0.254"] = ["150.0.0.254", "7", "9"]
###############Table prefix creation###############
tableprefix=[]
label=1
for i in switch:
    ############zero padding for 32 bit#############
    binIP = str((bin(int(ipaddress.IPv4Address(i)))))[2:]
    a = len(binIP)
    fullBinary = int((32 - a)) * str(0) + binIP
    ############cutting the prefix with the netmask##############
    prefix=[fullBinary[:int(switch[i][SUBNET])], label, switch[i][IP]]
    tableprefix.append(prefix)
#####Put in Order the table Prefix and add label######
for i in range(0,len(tableprefix)-1):
        for j in range(i,len(tableprefix)):
            if tableprefix[i][0].__len__() > tableprefix[j][0].__len__():
                temp = tableprefix[i]
                tableprefix[i] = tableprefix[j]
                tableprefix[j] = temp
        tableprefix[i][1] = label
        label += 1
tableprefix[i+1][1] = label
print("----------Prefix Table-----------------")
for prefix in tableprefix:
    print(prefix)


###################CREATE THE HASH TABLE##########################################################
hash_table = []
longest_prfx = len(tableprefix[label-1][0])#take the lenght of the last prefix in the table that corresponds to the largest prefix
for i in range(0,longest_prfx+1):#take i as the lenght of each possible prefix form 0 to the longest one
    hash_table.append([])
    for j in tableprefix:#for each prefix in the table
        if i == len(j[0]):#if the lenght of the prefix correspond to the courrent lenght we append it
            hash_table[i].append(j[0])
        elif i < len(j[0]):#since the prefix table is in order, if the variable i is less than the courrent prefix lenght it is no necessary to look all the following prefixes
            break
###############################CONSTRUCT THE TREE#######################################
tree = Tree()
midle = int(len(hash_table)/2)
lenght = int(len(hash_table))
tree.construct(-1, midle, lenght,hash_table)
tree.addmarkers(hash_table, lenght)#Adding the markers
tree.addBMP(hash_table, lenght)
print("\n----------Hash Table-----------------")
print(hash_table)
#x="1234567bmp"
#print(x[-3:])
#print(x[:-3])

########################################LOOKUP##########################################
dst_ip=input('Enter your input:')#Here we must send an IP direction
############zero padding for 32 bit#############
c = str((bin(int(ipaddress.IPv4Address(dst_ip)))))[2:]
d = len(c)
ipsearch = int((32 - d)) * str(0) + c
print(ipsearch)
x=tree.lookup(hash_table, ipsearch)
#print (x)
hash=[w[:x] for w in hash_table[x]]#sliced the prefixes to teak of the m in the resulting hash table
for i in tableprefix:#searh and return the next hop ip finfing its correspondent prefix.
    if hash_table[x][hash.index(ipsearch[:x])][:x] == i[0]:
        print (i[2])