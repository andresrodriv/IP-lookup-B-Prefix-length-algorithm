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

########Class for creating the binary trie################
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
##############################GENERATION OF THE TRIE###################################################################
		tableprefix = []
		label = 1
		for i in self.switch:
			############zero padding for 32 bit#############
			binIP = str((bin(int(ipaddress.IPv4Address(unicode(i))))))[2:]  # unicode for the IPv4 Address formatting
			length_binIP = len(binIP)
			fullBinary = int((32 - length_binIP)) * str(0) + binIP
			############cutting the prefix with the netmask##############
			prefix = [fullBinary[:int(self.switch[i][SUBNET])], label, self.switch[i][IP]]
			tableprefix.append(prefix)
		#####Put in Order the table Prefix and add a label######
		for i in range(0, len(tableprefix) - 1):
			for j in range(i, len(tableprefix)):
				if tableprefix[i][0].__len__() > tableprefix[j][0].__len__():
					temp = tableprefix[i]
					tableprefix[i] = tableprefix[j]
					tableprefix[j] = temp
			tableprefix[i][1] = label
			label += 1
		tableprefix[i + 1][1] = label
		############CREATE THE TRIE#################################################
		self.trie = Trie('gray', '0')
		for i in tableprefix:
			self.trie.insert(i)
#######################################################################################################################
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
########################################################################################################################
			# PACKET CLASSIFICATION FUNCTION: it returns action: "allow" or "deny"
			# action_rule = self.linear_classification(src_ip, dst_ip, proto, sport, dport)
			action_rule = "allow"	
			
			if action_rule == "allow":			
				# IP LOOKUP FUNCTION: it is zero if it didn't find a solution
				destination_switch_IP = self.binary_trie_search(dst_ip)
########################################################################################################################
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
####################Binary LOOKUP######################################################################################
	def binary_trie_search(self, dst_ip):
		self.logger.info(" --- Binary Search")
		self.logger.info("Destination IP: %s", dst_ip)
		############zero padding for 32 bit#############
		bin_dst_ip = str((bin(int(ipaddress.IPv4Address(unicode(dst_ip))))))[2:]
		length_bin_dst_ip = len(bin_dst_ip)
		ipsearch = int((32 - length_bin_dst_ip)) * str(0) + bin_dst_ip
		################################################
		NextHop = self.trie.lookupsearch(ipsearch)
		self.logger.info("Next Hop Returned: %s", NextHop)
		return NextHop
########################################################################################################################
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