from ryu.base import app_manager
from ryu.controller import ofp_event
from ryu.controller import dpset
from ryu.controller import ofp_event
from ryu.controller.handler import CONFIG_DISPATCHER, MAIN_DISPATCHER
from ryu.app.wsgi import ControllerBase, WSGIApplication, route
from ryu.controller.handler import set_ev_cls
from ryu.ofproto import ofproto_v1_3
from ryu.lib.packet import packet
from ryu.lib.packet import ethernet
from ryu.lib.packet import ether_types
from ryu.topology.api import get_switch, get_link, get_host, get_all_host
from ryu.topology import event, switches 
import networkx as nx
import json
import logging
import struct
import ipaddress# For removing the dots in the IP Address
from webob import Response
from ryu.lib.mac import haddr_to_bin
from ryu.lib.packet.packet import Packet
from ryu.lib.packet import arp
from ryu.lib.packet import ipv4
from ryu.lib.packet import tcp
from ryu.lib.packet import udp
from ryu.ofproto import ether
from ryu.app.ofctl.api import get_datapath

# Packet Classification parameters
SRC_IP = 0
DST_IP = 1
PROTO  = 2
SPORT  = 3
DPORT  = 4
ACTION = 5

# IP lookup parameters
IP     = 0
SUBNET = 1
DPID   = 2

# Topologies
TOPO = 2

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
class SimpleSwitch13(app_manager.RyuApp):
	OFP_VERSIONS = [ofproto_v1_3.OFP_VERSION]
	_CONTEXTS = {'wsgi': WSGIApplication}
	
	def __init__(self, *args, **kwargs):
		super(SimpleSwitch13, self).__init__(*args, **kwargs)
		wsgi = kwargs['wsgi']
		self.topology_api_app = self
		self.net = nx.DiGraph()
		self.nodes = {}
		self.links = {}
		self.no_of_nodes = 0
		self.no_of_links = 0		
		self.datapaths = []
		self.switch_id = []
		self.mac_to_port = {}
		self.mac_to_dpid = {}
		self.port_to_mac = {}
		self.i=0
		
		# Packet Classification initial parameters
		
		self.classify = {}
		self.classify["r1"] = ["195.0.0.1","128.128.0.1","6","*","1234","allow"]
		self.classify["r2"] = ["128.128.0.1","195.0.0.1","6","1234","*","allow"]
		self.classify["r3"] = ["195.0.0.1","128.128.0.1","1","*","*","allow"]
		self.classify["r4"] = ["128.128.0.1","195.0.0.1","1","*","*","allow"]
		self.classify["r5"] = ["*","*","*","*","*","deny"]
 
		self.counters = {} 
		self.counters["r1"] = 0                           
		self.counters["r2"] = 0                           
		self.counters["r3"] = 0                           
		self.counters["r4"] = 0                           
		self.counters["r5"] = 0       
		
		if TOPO == 1:			
			self.switch = {}
			self.switch["195.0.0.254"  ] = ["195.0.0.254","8","1"] 
			self.switch["128.128.0.254"] = ["128.128.0.254","12","2"] 
			self.switch["154.128.0.254"] = ["154.128.0.254","16","3"] 

			self.lookup = {}
			self.lookup["195.0.0.1"]   = "195.0.0.254"
			self.lookup["195.0.0.2"]   = "195.0.0.254"
			self.lookup["128.128.0.1"] = "128.128.0.254"
			self.lookup["128.128.0.2"] = "128.128.0.254"
			self.lookup["154.128.0.1"] = "154.128.0.254"
			self.lookup["154.128.0.2"] = "154.128.0.254"
			
			self.ip_to_mac = {}
			self.ip_to_mac["195.0.0.1"]   = "00:00:00:00:00:01"
			self.ip_to_mac["195.0.0.2"]   = "00:00:00:00:00:02"
			self.ip_to_mac["128.128.0.1"] = "00:00:00:00:00:03"
			self.ip_to_mac["128.128.0.2"] = "00:00:00:00:00:04"
			self.ip_to_mac["154.128.0.1"] = "00:00:00:00:00:05"
			self.ip_to_mac["154.128.0.2"] = "00:00:00:00:00:06"
		
		elif TOPO == 2:
			self.switch = {}
			self.switch["195.0.0.254"  ]   = ["195.0.0.254","8","1"] 
			self.switch["128.128.0.254"]   = ["128.128.0.254","12","2"] 
			self.switch["154.128.0.254"]   = ["154.128.0.254","16","3"] 
			self.switch["197.160.0.254"]   = ["197.160.0.254","24","4"]
			self.switch["192.168.0.254"]   = ["192.168.0.254","24","5"]	
			self.switch["192.169.0.254"]  = ["192.169.0.254","24","6"]
			self.switch["192.170.0.254"]  = ["192.170.0.254","24","7"]

			self.lookup = {}
			self.lookup["195.0.0.1"]     = "195.0.0.254"
			self.lookup["195.0.0.2"]     = "195.0.0.254"
			self.lookup["128.128.0.1"]   = "128.128.0.254"
			self.lookup["154.128.0.1"]   = "154.128.0.254"
			self.lookup["197.160.0.1"]   = "197.160.0.254"
			self.lookup["192.168.0.1"]   = "192.168.0.254"
			self.lookup["192.169.0.1"]  = "192.169.0.254"
			self.lookup["192.170.0.1"]  = "192.170.0.254"

			
			self.ip_to_mac = {}
			self.ip_to_mac["195.0.0.1"]     = "00:00:00:00:00:01"
			self.ip_to_mac["195.0.0.2"]     = "00:00:00:00:00:02"
			self.ip_to_mac["128.128.0.1"]   = "00:00:00:00:00:03"
			self.ip_to_mac["154.128.0.1"]   = "00:00:00:00:00:04"
			self.ip_to_mac["197.160.0.1"]   = "00:00:00:00:00:05"
			self.ip_to_mac["192.168.0.1"]   = "00:00:00:00:00:06"
			self.ip_to_mac["192.169.0.1"]  = "00:00:00:00:00:07"
			self.ip_to_mac["192.170.0.1"]  = "00:00:00:00:00:08"
##############################GENERATION OF THE HASH TABLE###################################################################
		self.tableprefix = []
		label = 1
		for i in self.switch:
			############zero padding for 32 bit#############
			binIP = str((bin(int(ipaddress.IPv4Address(unicode(i))))))[2:]  # unicode for the IPv4 Address formatting
			length_binIP = len(binIP)
			fullBinary = int((32 - length_binIP)) * str(0) + binIP
			############cutting the prefix with the netmask##############
			prefix = [fullBinary[:int(self.switch[i][SUBNET])], label, self.switch[i][IP]]
			self.tableprefix.append(prefix)
		#####Put in Order the table Prefix and add a label######
		for i in range(0, len(self.tableprefix) - 1):
			for j in range(i, len(self.tableprefix)):
				if self.tableprefix[i][0].__len__() > self.tableprefix[j][0].__len__():
					temp = self.tableprefix[i]
					self.tableprefix[i] = self.tableprefix[j]
					self.tableprefix[j] = temp
			self.tableprefix[i][1] = label
			label += 1
		self.tableprefix[i + 1][1] = label
		# for prefix in self.tableprefix:
		#    print(prefix)

		###################CREATE THE HASH TABLE##########################################################
		self.hash_table = []
		longest_prfx = len(self.tableprefix[label - 1][0])  # take the lenght of the last prefix in the table that corresponds to the largest prefix
		# print(longest_prfx)
		for i in range(0, longest_prfx + 1):  # take i as the lenght of each possible prefix form 0 to the longest one
			self.hash_table.append([])  # create an array inside every i i = hash table, j = prefixes
			for j in self.tableprefix:  # for each prefix in the table
				if i == len(j[0]):  # if the lenght of the prefix correspond to the courrent lenght we append it
					self.hash_table[i].append(j[0])
				elif i < len(j[0]):  # since the prefix table is in order, if the variable i is less than the courrent prefix lenght it is no necessary to look all the following prefixes
					break
		# print(hash_table)
		self.hash_table = list(filter(None, self.hash_table))
		###############################CONSTRUCT THE TREE#######################################
		self.tree = Tree()
		midle = int(len(self.hash_table) / 2)
		lenght = int(len(self.hash_table))
		self.tree.construct(-1, midle, lenght, self.hash_table)
		# print(hash_table)
		self.tree.addmarkers(self.hash_table, lenght)  # Adding the markers
		# print(hash_table)
		self.tree.addBMP(self.hash_table, lenght)
###############################################################################################################################################################
	def ls(self,obj):
		print("\n".join([x for x in dir(obj) if x[0] != "_"]))
		
		
	def send_arp(self, datapath, opcode, srcMac, srcIp, dstMac, dstIp, outPort):
		if opcode == 1:
			targetMac = "00:00:00:00:00:00"
			targetIp = dstIp
		elif opcode == 2:
			targetMac = dstMac
			targetIp = dstIp

		e = ethernet.ethernet(dstMac, srcMac, ether.ETH_TYPE_ARP)
		a = arp.arp(1, 0x0800, 6, 4, opcode, srcMac, srcIp, targetMac, targetIp)
		p = Packet()
		p.add_protocol(e)
		p.add_protocol(a)
		p.serialize()

		actions = [datapath.ofproto_parser.OFPActionOutput(outPort, 0)]
		out = datapath.ofproto_parser.OFPPacketOut(
			datapath=datapath,
			buffer_id=0xffffffff,
			in_port=datapath.ofproto.OFPP_CONTROLLER,
			actions=actions,
			data=p.data)
		datapath.send_msg(out)

		
	@set_ev_cls(ofp_event.EventOFPSwitchFeatures, CONFIG_DISPATCHER)
	def switch_features_handler(self, ev):
		datapath = ev.msg.datapath
		ofproto = datapath.ofproto
		parser = datapath.ofproto_parser
		msg = ev.msg
		self.datapaths.append(msg.datapath)
		self.switch_id.append(msg.datapath_id)
		
		match = parser.OFPMatch()
		actions = [parser.OFPActionOutput(ofproto.OFPP_CONTROLLER,
										ofproto.OFPCML_NO_BUFFER)]
		self.add_flow(datapath, 0, match, actions)
		
	def add_flow(self, datapath, priority, match, actions, buffer_id=None):
		ofproto = datapath.ofproto
		parser = datapath.ofproto_parser

		inst = [parser.OFPInstructionActions(ofproto.OFPIT_APPLY_ACTIONS,
                                             actions)]
		if buffer_id:
			mod = parser.OFPFlowMod(datapath=datapath, buffer_id=buffer_id,
                                    priority=priority, match=match,
                                    instructions=inst)
		else:
			mod = parser.OFPFlowMod(datapath=datapath, priority=priority,
                                    match=match, instructions=inst)
		datapath.send_msg(mod)

	@set_ev_cls(ofp_event.EventOFPPacketIn, MAIN_DISPATCHER)
	def _packet_in_handler(self, ev):
        
		if ev.msg.msg_len < ev.msg.total_len:
			self.logger.debug("packet truncated: only %s of %s bytes",
                              ev.msg.msg_len, ev.msg.total_len)
		msg = ev.msg
		datapath = msg.datapath
		ofproto = datapath.ofproto
		parser = datapath.ofproto_parser
		in_port = msg.match['in_port']		

		pkt = packet.Packet(msg.data)
		eth = pkt.get_protocols(ethernet.ethernet)[0]

		if eth.ethertype == ether_types.ETH_TYPE_LLDP:
            # ignore lldp packet
			return
		dst = eth.dst
		src = eth.src
		
		dpid_src = datapath.id
		
		# TOPOLOGY DISCOVERY------------------------------------------
		
		switch_list = get_switch(self.topology_api_app, None)   
		switches=[switch.dp.id for switch in switch_list]		
		self.net.add_nodes_from(switches)
		links_list = get_link(self.topology_api_app, None)
		links=[(link.src.dpid,link.dst.dpid,{'port':link.src.port_no}) for link in links_list]
		self.net.add_edges_from(links)
		links=[(link.dst.dpid,link.src.dpid,{'port':link.dst.port_no}) for link in links_list]
		self.net.add_edges_from(links)
		# print links
		
		# MAC LEARNING-------------------------------------------------
		
		self.mac_to_port.setdefault(dpid_src, {})
		self.mac_to_port.setdefault(src, {})
		self.port_to_mac.setdefault(dpid_src, {})
		self.mac_to_port[dpid_src][src] = in_port	
		self.mac_to_dpid[src] = dpid_src
		self.port_to_mac[dpid_src][in_port] = src
		self.logger.info("Packet in the controller from switch: %s", dpid_src)
		#print self.mac_to_port
		
		# HANDLE ARP PACKETS--------------------------------------------
		
		if eth.ethertype == ether_types.ETH_TYPE_ARP:
			arp_packet = pkt.get_protocol(arp.arp)
			arp_dst_ip = arp_packet.dst_ip
			arp_src_ip = arp_packet.src_ip
			# self.logger.info("ARP packet from switch: %s source IP: %s destination IP: %s from port: %s", dpid_src, arp_src_ip, arp_dst_ip, in_port)
			# self.logger.info("ARP packet from switch: %s source MAC: %s destination MAC:%s from port: %s", dpid_src, src, dst, in_port)
			
			if arp_dst_ip in self.ip_to_mac:
				if arp_packet.opcode == 1:
					# send arp reply (SAME SUBNET)
					dstIp = arp_src_ip
					srcIp = arp_dst_ip
					dstMac = src
					srcMac = self.ip_to_mac[arp_dst_ip]
					outPort = in_port
					opcode = 2 # arp reply packet
					self.send_arp(datapath, opcode, srcMac, srcIp, dstMac, dstIp, outPort)
			else:
				if arp_packet.opcode == 1:
					# send arp reply (GATEWAY)
					dstIp = arp_src_ip
					srcIp = arp_dst_ip
					dstMac = src
					srcMac = self.port_to_mac[dpid_src][in_port]
					outPort = in_port
					opcode = 2 # arp reply packet
					self.send_arp(datapath, opcode, srcMac, srcIp, dstMac, dstIp, outPort)
		
		# HANDLE IP PACKETS----------------------------------------------- 	
		
		ip4_pkt = pkt.get_protocol(ipv4.ipv4)
		if ip4_pkt:
			src_ip = ip4_pkt.src
			dst_ip = ip4_pkt.dst
			proto  = str(ip4_pkt.proto)
			sport = "0"
			dport = "0" 
			if proto == "6":
				tcp_pkt = pkt.get_protocol(tcp.tcp)
				sport = str(tcp_pkt.src_port)
				dport = str(tcp_pkt.dst_port)
			   
			if proto == "17":
				udp_pkt = pkt.get_protocol(udp.udp)
				sport = str(udp_pkt.src_port)
				dport = str(udp_pkt.dst_port)
				
			self.logger.info("Packet from the switch: %s, source IP: %s, destination IP: %s, From the port: %s", dpid_src, src_ip, dst_ip, in_port)
#######################################################################################################################################################			
			# PACKET CLASSIFICATION FUNCTION: it returns action: "allow" or "deny"
			# action_rule = self.linear_classification(src_ip, dst_ip, proto, sport, dport)
			action_rule = "allow"	
			
			if action_rule == "allow":			
				# IP LOOKUP FUNCTION: it is zero if it didn't find a solution
				destination_switch_IP = self.prefix_lenght_search(dst_ip)
#######################################################################################################################################################				
				if destination_switch_IP != "0":
					datapath_dst = get_datapath(self,int(self.switch[destination_switch_IP][DPID]))
					dpid_dst = datapath_dst.id			
					self.logger.info(" --- Destination present on switch: %s", dpid_dst)
					
					# Shortest path computation
					path = nx.shortest_path(self.net,dpid_src,dpid_dst)
					self.logger.info(" --- Shortest path: %s", path)
					
					if len(path) == 1:
						In_Port = self.mac_to_port[dpid_src][src]
						Out_Port = self.mac_to_port[dpid_dst][dst]	
						actions_1 = [datapath.ofproto_parser.OFPActionOutput(Out_Port)]
						actions_2 = [datapath.ofproto_parser.OFPActionOutput(In_Port)]
						match_1 = parser.OFPMatch(in_port=In_Port, eth_dst=dst)
						self.add_flow(datapath, 1, match_1, actions_1)

						actions = [datapath.ofproto_parser.OFPActionOutput(Out_Port)]
						data = msg.data
						pkt = packet.Packet(data)
						eth = pkt.get_protocols(ethernet.ethernet)[0]
						# self.logger.info(" --- Changing destination mac to %s" % (eth.dst))
						pkt.serialize()
						out = datapath.ofproto_parser.OFPPacketOut(
							datapath=datapath, buffer_id=0xffffffff, in_port=datapath.ofproto.OFPP_CONTROLLER,
							actions=actions, data=pkt.data)
						datapath.send_msg(out)
						
						
					elif len(path) == 2:				
						path_port = self.net[path[0]][path[1]]['port']
						actions = [datapath.ofproto_parser.OFPActionOutput(path_port)]
						data = msg.data
						pkt = packet.Packet(data)
						eth = pkt.get_protocols(ethernet.ethernet)[0]
						eth.src = self.ip_to_mac[src_ip] 
						eth.dst = self.ip_to_mac[dst_ip] 
						# self.logger.info(" --- Changing destination mac to %s" % (eth.dst))
						pkt.serialize()
						out = datapath.ofproto_parser.OFPPacketOut(
						datapath=datapath, buffer_id=0xffffffff, in_port=datapath.ofproto.OFPP_CONTROLLER,
							actions=actions, data=pkt.data)
						datapath.send_msg(out)	
						
					elif len(path) > 2:
						# Add flows in the middle of the network path 
						for i in range(1, len(path)-1):							
							In_Port = self.net[path[i]][path[i-1]]['port']
							Out_Port = self.net[path[i]][path[i+1]]['port']
							dp = get_datapath(self, path[i])
							# self.logger.info("Matched OpenFlow Rule = switch: %s, from in port: %s, to out port: %s, source IP: %s, and destination IP: %s", path[i], In_Port, Out_Port, src_ip, dst_ip)
						
							actions_1 = [dp.ofproto_parser.OFPActionOutput(Out_Port)]
							match_1 = parser.OFPMatch(in_port=In_Port, eth_type = 0x0800, ipv4_src=src_ip, ipv4_dst=dst_ip)
							self.add_flow(dp, 1, match_1, actions_1)
						
						path_port = self.net[path[0]][path[1]]['port']
						actions = [datapath.ofproto_parser.OFPActionOutput(path_port)]
						data = msg.data
						pkt = packet.Packet(data)
						eth = pkt.get_protocols(ethernet.ethernet)[0]
						# change the mac address of packet
						eth.src = self.ip_to_mac[src_ip] 
						eth.dst = self.ip_to_mac[dst_ip] 
						# self.logger.info(" --- Changing destination mac to %s" % (eth.dst))
						pkt.serialize()
						out = datapath.ofproto_parser.OFPPacketOut(
						datapath=datapath, buffer_id=0xffffffff, in_port=datapath.ofproto.OFPP_CONTROLLER,
							actions=actions, data=pkt.data)
						datapath.send_msg(out)

	@set_ev_cls(event.EventSwitchEnter)
	def get_topology_data(self, ev):
		switch_list = get_switch(self.topology_api_app, None)   
		switches=[switch.dp.id for switch in switch_list]		
		self.net.add_nodes_from(switches)
		links_list = get_link(self.topology_api_app, None)
		links=[(link.src.dpid,link.dst.dpid,{'port':link.src.port_no}) for link in links_list]
		self.net.add_edges_from(links)
		links=[(link.dst.dpid,link.src.dpid,{'port':link.dst.port_no}) for link in links_list]
		self.net.add_edges_from(links)		
		# print "**********List of links"
		# print self.net.edges()
        #for link in links_list:
	    #print link.dst
            #print link.src
            #print "Novo link"
	    #self.no_of_links += 1		

#-------------------------------------------------------------------------------------------------------
		
	def linear_search(self, dst_ip):
		self.logger.info(" --- IP address Lookup") 
		if dst_ip in self.lookup:
			destination_switch_IP = self.lookup[dst_ip]
			return destination_switch_IP
		else:
			destination_switch_IP = "0"
			return destination_switch_IP
####################Binary Lenght Search######################################################################################
	def prefix_lenght_search(self, dst_ip):
		self.logger.info(" --- Prefix lenght Search")
		self.logger.info("Destination IP: %s", dst_ip)
		############zero padding for 32 bit#############
		bin_dst_ip = str((bin(int(ipaddress.IPv4Address(unicode(dst_ip))))))[2:]
		length_bin_dst_ip = len(bin_dst_ip)
		ipsearch = int((32 - length_bin_dst_ip)) * str(0) + bin_dst_ip
		##############################################################
		x = self.tree.lookup(self.hash_table, ipsearch)
		hash = [w[:len(self.hash_table[x][0])] for w in self.hash_table[x]]  # slice the prefixes to take of the m in the resulting hash table
		for i in self.tableprefix:  # searh and return the next hop ip finfing its correspondent prefix.
			if self.hash_table[x][hash.index(ipsearch[:len(self.hash_table[x][0])])][:len(self.hash_table[x][0])] == i[0]:
				self.logger.info("Next Hop Returned: %s", i[2])
				return i[2]
###############################################################################################################################
	def linear_classification(self, src_ip, dst_ip, proto, sport, dport):
		action = "deny"
		self.logger.info(" --- Packet classification") 

		# check matching rule
		for rule in sorted(self.classify):
			match = self.classify[rule]
			if (match[SRC_IP] == src_ip or match[SRC_IP] == "*") and \
				(match[DST_IP] == dst_ip or match[DST_IP] == "*") and \
				(match[PROTO]  == proto  or match[PROTO]  == "*") and \
				(match[SPORT]  == sport  or match[SPORT]  == "*") and \
				(match[DPORT]  == dport  or match[DPORT]  == "*") :
				self.logger.info(" --- Packet matched rule %s. Action is %s" % (rule, match[ACTION]))
				action = match[ACTION]
				self.counters[rule] = self.counters[rule] + 1
				return action
		
		return action
	
	
	
app_manager.require_app('ryu.app.ws_topology')
app_manager.require_app('ryu.app.ofctl_rest')
app_manager.require_app('ryu.app.gui_topology.gui_topology')		