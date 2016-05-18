from LogManager import LoggingManager
from lustreParser import LParser
from pyparsing import ParseException
from kindInterface import PkindJobs, KindUtil
from lustreNodes import BuildLusteNode
from ccNodes import CcNodes
import pprint
import config
import os
import xml.etree.ElementTree as ET

pp = pprint.PrettyPrinter(indent=4)


 
class CompositionalJobs(object):
    """ Compositional verifier main executor """
    def __init__(self):
        self._log = LoggingManager.get_logger(__name__)
        self.inv_options = config.INV_OPTIONS
        self.invBank = {}
        self.kindUtil = KindUtil()
        self.componentProps = None
        return
 

    def verifyProps(self, lusFile, allNodes, timeout, pkindOptions, componentProps):
        self._log.info("Verifing %s", str(lusFile))
        self.componentProps = componentProps
        pkind = PkindJobs()
        pkind.PropertyResult = self.propResult
        self.res = "<pkind>\n\n"
        for node in allNodes:
            cmd = ["pkind", "-compression", "-with-inv-gen", node]
            pkind.runJobs(node, node, cmd, timeout)
        self.res += "</pkind>\n"
        self._log.info("Finished getting results.")

    
    def propResult(self, result):
        self._log.debug("Results from Kind verification")
        try:
            self.parseXML(result)
        except Exception as e:
            self._log.exception(str(e))

    def parseXML(self, result):
        self._log.debug("Parsing XML Result")
        for node_name, r in result.items():
            self.res += "<node name='"+ str(node_name) + "'>\n\n"
            self.res += "<inv>\n";
            self.res += "<![CDATA["
            self.res += self.kindUtil.mkInv(str(node_name)).decode()
            self.res += "]]>\n";
            self.res += "</inv>\n";
            line, sep, text = r.partition("\n")
            if "?xml" in line:
              r = text
            self.res += r
            self.res += "</node>\n\n"

   
            
class NodeComposer(object):
    """ Given a multi-node Lustre file it make the composition of nodes"""
    
    def __init__(self):
        self._log = LoggingManager.get_logger(__name__)
        self.LustreAST = {}
        self.kindUtil = KindUtil()
        self.d = None
        self.componentsNode = {}
        return
    
    def parseFile(self, lusFile):
        self._log.info("Parsing Lustre file: %s" % lusFile)
        parser = LParser()
        with open(lusFile, 'r') as f:
            try:
                self.LustreAST= parser.parse(f.read())
                self._log.debug(parser.ppAST(self.LustreAST))
                return True
            except ParseException, err:
                self._log.exception(str(err))
                return False
        
    def tgDecompose(self, lusFile, invariants):
        componentProps = {}
        multiNodes = {} # keep track of node calls inside a node
        anyPropNodes = {} # keep track if a node has propoerty to be verified
        if self.parseFile(lusFile):
            self._log.info("Successful parse")
            nodeNames = self.LustreAST.keys()
            mk_node = CcNodes(nodeNames)
            for n,d in self.LustreAST.iteritems():
                if n == "glob":
                    pass
                else:
                    node, prop_dict, extraNodes, anyProp = mk_node.tgLustre(d, invariants)
                    if node is not None:
                        self.componentsNode.update({n:node})
                        componentProps.update({n:prop_dict})
                        multiNodes.update({n:extraNodes})
                        anyPropNodes.update({n:anyProp})
                    else:
                        self._log.exception("Building nodes")
            nodes = self.handleMultiNodes(multiNodes)
            return nodes, componentProps, multiNodes, anyPropNodes
        else:
            self._log.error("Parsing error")
            return None, None, None

    def ccDecompose(self, lusFile):
        componentProps = {}
        multiNodes = {} # keep track of node calls inside a node
        anyPropNodes = {} # keep track if a node has propoerty to be verified
        if self.parseFile(lusFile):
            self._log.info("Successful parse")
            nodeNames = self.LustreAST.keys()
            mk_node = CcNodes(nodeNames)
            for n,d in self.LustreAST.iteritems():
                if n == "glob":
                    pass
                else:
                    node, prop_dict, extraNodes, anyProp = mk_node.ccLustre(d)
                    if node is not None:
                        self.componentsNode.update({n:node})
                        componentProps.update({n:prop_dict})
                        multiNodes.update({n:extraNodes})
                        anyPropNodes.update({n:anyProp})
                    else:
                        self._log.exception("Building nodes")
            nodes = self.handleMultiNodes(multiNodes)
            return nodes, componentProps, multiNodes, anyPropNodes
        else:
            self._log.error("Parsing error")
            return None, None, None

    def handleMultiNodes(self, multiNodes):
        self._log.debug("Handling Multi Nodes")
        out_nodes = {}
        for n, nodes in self.componentsNode.iteritems():
            if (multiNodes[n] != []) and (multiNodes[n] != None):
                node = self.flattenNodes(nodes, multiNodes[n])
                out_nodes.update({n:node})
            else:
                out_nodes.update({n:nodes})
        return out_nodes

    def flattenNodes(self, mainNode, extraNodes):
        self._log.debug("Flattening nodes")
        nodes = mainNode + "\n"
        for n in extraNodes:
            node = self.componentsNode[n]
            nodes += node
        flatnode = self.kindUtil.runLsimplify(nodes)
        return flatnode


    def storeNodes(self, lusDir, lustreNodes, componentProps, anyPropNodes):
        self._log.debug("Storing Nodes")
        allNodes = []
        compProps = {}
        self.d = ((lusDir.split("."))[0] + "_LUSTRE")
        if not os.path.exists(self.d):
            os.makedirs(self.d)
        for node_name, node in lustreNodes.iteritems():
            if node and anyPropNodes[node_name]:
                f_node = self.d+os.sep+node_name+".lus"
                allNodes.append(f_node)
                compProps.update({f_node: componentProps[node_name]})
                f = open(f_node, "w+")
                f.write(node)
                f.close()
        return allNodes, compProps
            


class NodeSynth(object):
    def __init__(self, contractChecker, pkindOption, lusFile, timeout):
        self.timeout = timeout
        self._file = lusFile
        self._options = pkindOption
        self._contractChecker = contractChecker
        self._log = LoggingManager.get_logger(__name__)
        return
  
    def run(self):
        self._log.debug("Running the main compositional executor")
        composer = NodeComposer()
        runner = CompositionalJobs()
        nodes = None
        try:
            if self._contractChecker:
                self._log.info("Composing Lustre nodes for contract checking")
                nodes, componentProps, multiNodes, anyPropNodes = composer.ccDecompose(self._file)
            else:
                self._log.info("Composing Lustre nodes for property checking")
                nodes = composer.decompose(self._file)
            if nodes and componentProps and multiNodes:
                allNodes, compProps = composer.storeNodes(self._file, nodes, componentProps, anyPropNodes)
                runner.verifyProps(self._file, allNodes, self.timeout, self._options, compProps)
        except Exception as e:
            self._log.exception(str(e))
        return runner.res




            
        

