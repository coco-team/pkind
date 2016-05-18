from LogManager import LoggingManager
import json
from nodeDecomposer import NodeComposer
from kindInterface import KindUtil

class TraceExecutor (object):

	def __init__(self):
		self._log = LoggingManager.get_logger(__name__)
		return

	def run(self, jsonFile):
		self._log.info('Running ' + str(jsonFile))
		try:
			json_data = self.readJson(jsonFile)
			for node, test in json_data.iteritems():
				self._log.info("Running Test for node: " + str(node))
		except Exception as e:
			self._log.exception(str(e))


	def readJson(self, jsonFile):
		self._log.info("Reading " + str(jsonFile))
		with open(jsonFile, 'r') as f:
			json_data = json.load(f)
		return json_data



class TestGeneration(object):
    def __init__(self):
        self._log = LoggingManager.get_logger(__name__)
        self.composer = NodeComposer()
        self.kind = KindUtil()
        return

    def preamble(self, lusFile):
        self._log.info("Preamble")
        nodes = None
        try:
            nodes, componentProps, multiNodes, anyPropNodes = self.composer.ccDecompose(lusFile)
            if nodes and componentProps and multiNodes:
                allNodes, compProps = self.composer.storeNodes(lusFile, nodes, componentProps, anyPropNodes)
                return allNodes
        except Exception as e:
            self._log.exception(str(e))
            return None

    def generateTestCase(self, lusFile):
    	allNodes = self.preamble(lusFile)
    	if allNodes:
    	   nodesWithInv = self.generateInvariants(lusFile, allNodes)
           if nodesWithInv:
            for node in nodesWithInv:
                testCases = self.kind.runTestGen(node)
                print testCases
        else:
            self._log.error("No invariants generated")
    	return
 	

    def preamble(self, lusFile):
    	self._log.info("Preamble")
        nodes = None
        try:
            nodes, componentProps, multiNodes, anyPropNodes = self.composer.ccDecompose(lusFile)
            if nodes and componentProps and multiNodes:
                allNodes, compProps = self.composer.storeNodes(lusFile, nodes, componentProps, anyPropNodes)
                return allNodes
        except Exception as e:
            self._log.exception(str(e))
            return None


    def generateInvariants(self, lusFile, allNodes):
    	self._log.info("Generating Invariants")
    	invariants = None
    	for node in allNodes:
    		invariants = self.kind.runInvGen(node)
    		print invariants
    		nodes, componentProps, multiNodes, anyPropNodes = self.composer.tgDecompose(lusFile, invariants)
           	if nodes and componentProps and multiNodes:
                    allNodes, compProps = self.composer.storeNodes(lusFile, nodes, componentProps, anyPropNodes)
                    return allNodes



	











