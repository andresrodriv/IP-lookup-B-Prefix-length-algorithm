import ipaddress

###DEFINED FUNCTIONS AND CLASSES
class Trie:
    def __init__(self, color, label):
        self.left = None #At the start of the trie we do not have nodes in the right or in the left
        self.right = None
        self.father = None
        self.destination_switch_IP = '0'#switch associated with the prefix
        self.color = color #Used to indicate if the node is gray or white
        self.label = label #the label corresponding to the prefix label
# Insert one ip prefix
    def insert(self, prefix):
        node=self
        #print(prefix)
        for i in prefix[0]:#for each bit in the prefix
            if i == '0':
                if node.left is None:#if there is no node in the left create one
                    node.left = Trie('white', None)#initialize as a white node
                    node.left.father = node#for the created node, the father node is the courrent one
                    node = node.left
                else:
                    node = node.left#if there already exists a node, point to it
            elif i == '1':
                if node.right is None:#if there is no node in the right create one
                    node.right = Trie('white', None)
                    node.right.father = node
                    node = node.right
                else:
                    node = node.right#if there already exists a node, point to it
        node.color = 'gray'#when the prefis ends, the current node is a gray one
        node.label = prefix[1]#this node saves the label of the prefix
        node.destination_switch_IP = prefix[2]#this node saves the correspondent IP of the prefix
# lookup function
    def lookupsearch(self, lookup):
        node = self#Start pointing at the first node
        for i in lookup:#For each bit in the ip direction to be searched
            if node.right or node.left:#We assure that there is a node under the current node
                if i == '1' and node.right:#In case the bit of the ip direction is 1 and there is a node at the right we can continue
                    node = node.right
                elif i == '0' and node.left:#In case the bit of the ip direction is 0 and there is a node at the left we can continue
                    node = node.left
                else:
                    break
            else:
                break
        ##### Backtracking #####
        while node.color != 'gray':#We start in the final node and start pointing to the father of the nodes until find the las gray node, corresponding to a prefix
            node = node.father
        #print (node.destination_switch_IP)
        return node.destination_switch_IP#Return the Ip direction correspondent to the node of the found longest prefix
##################################################MAIN CODE ###################################################################
# IP lookup parameters
IP = 0
SUBNET = 1
DPID = 2

switch = {}
#####Prove Switches#############
switch["195.0.0.1"  ]   = ["195.0.0.254","8","1"]
switch["128.128.0.1"]   = ["128.128.0.254","12","2"]
switch["154.128.0.1"]   = ["154.128.0.254","16","3"]
switch["197.160.0.1"]   = ["197.160.0.254","24","4"]
switch["192.168.0.1"]   = ["192.168.0.254","24","5"]
switch["192.169.0.1"]  = ["192.169.0.254","24","6"]
switch["192.170.0.1"]  = ["192.170.0.254","24","7"]
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
############CREATE THE TRIE#################################################
trie = Trie('gray', '0')
for i in tableprefix:
    trie.insert(i)

########################################LOOKUP##########################################
dst_ip=input('Enter your input:')#Here we must send an IP direction
############zero padding for 32 bit#############
bin_dst_ip = str((bin(int(ipaddress.IPv4Address(dst_ip)))))[2:]
length_bin_dst_ip = len(bin_dst_ip)
ipsearch = int((32 - length_bin_dst_ip)) * str(0) + bin_dst_ip
print(ipsearch)
################################################
NextHop = trie.lookupsearch(ipsearch)
print (NextHop)
