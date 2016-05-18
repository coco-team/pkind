from LogManager import LoggingManager
import json
from nodeDecomposer import NodeComposer
from lustreParser import LParser
import random
from random import randint
from kindInterface import KindUtil
import os
from ccNodes import CcNodes
from pyparsing import ParseException
import xml.etree.ElementTree as ET


class RandomTestGeneration(object):
    def __init__(self):
        self._log = LoggingManager.get_logger(__name__)
        self.composer = NodeComposer()
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


    def compileAndRun(self, lusFile, depth, node):
        kind = KindUtil()
        try:
            result, cFile = kind.runCompiler(lusFile, node)
            if "C code generation" not in result:
                self._log.error("Error compiling" + str(lusFile))
            else:
                self._log.info("C file generated: " + str(cFile))
                tests = self.randomTests(lusFile,depth)
                d = os.path.dirname(lusFile)
                result, outFile = kind.runCCompiler(d, cFile)
                if result == "" and outFile:
                    self._log.info("Successfully compiled: " + outFile)
                    self.runTestCases(tests, outFile)
                else:
                    self._log.error("Compile")
        except Exception as e:
            self._log.exception(str(e))


    def randomTestGen(self, lusFile, depth, node):
        kind = KindUtil()
        rand_tests = open(lusFile+"_rand_tests", "w")
        try:
            tests = self.randomTests(lusFile,depth)
            for k, s in tests.iteritems():
                spl = " \n".join(x for x in s.split())
                rand_tests.write(spl+"\n")
            rand_tests.close()
            rand_test_file = os.path.abspath(lusFile+"_rand_tests")
            return rand_test_file
        except Exception as e:
            self._log.exception(str(e))
            return None


    def runTestCases(self, tests, prog):
        self._log.info("Running test cases for " + str(prog))
        kind = KindUtil()
        bin_dir = os.path.dirname(prog)
        try:
            testResult = kind.runTestCases(tests, prog)
            print testResult
        except Exception as e:
            print str(e)


    def randomTests(self, lusFile, depth):
        inputVars = []
        all_tests = {}
        if self.parseFile(lusFile):
            self._log.info("Successful parse")
            nodeNames = self.LustreAST.keys()
            for n,d in self.LustreAST.iteritems():
                if n == "glob":
                    pass
                else:
                    inputVars = d["input_vars"]
            for i in range(1, depth):
                test = self.randomize(inputVars, depth)
                all_tests.update({i: test})
            return all_tests
        else:
            self._log.error("Parsing error")
            return None


    def randomize(self, inputVars, depth):
        test_i = ""
        for var in inputVars:
            if var[1] == "bool":
                randBool = self.randBool()
                r_bool = "F" if str(randBool) == "False" else "T"
                test_i += r_bool + " "
            elif var[1] == "int":
                randInt = self.randInt()
                test_i += str(randInt) + " "
            elif var[1] == "real":
                randReal, randReal1 = self.randReal()
                test_i += (str(randReal) + "." + str(randReal1) + " ")
        return test_i


    def randBool(self):
        return bool(random.getrandbits(1))


    def randInt(self):
        return randint(0,50)


    def randReal(self):
        return randint(0,50), randint(0,10)


    def storeNodes(self, lusFile, nodeWithCondition):
        self._log.debug("Storing Nodes")
        f_node = lusFile+".tg"
        f = open(f_node, "w+")
        f.write(nodeWithCondition)
        f.close
        return f_node

        for node_name, node in lustreNodes.iteritems():
            if node and anyPropNodes[node_name]:
                f_node = self.d+os.sep+node_name+".lus"
                allNodes.append(f_node)
                compProps.update({f_node: componentProps[node_name]})
                f = open(f_node, "w+")
                f.write(node)
                f.close
        return allNodes, compProps


    def generateTestCaseCondition(self, lusFile, cond):
        inputVars = []
        all_tests = {}
        nodeWithCondition = None
        kind = KindUtil()
        if self.parseFile(lusFile):
            self._log.info("Successful parse")
            nodeNames = self.LustreAST.keys()
            mk_node = CcNodes(nodeNames)
            for n,d in self.LustreAST.iteritems():
                if n == "glob":
                    pass
                else:
                    nodeWithCondition, _, _, _ =  mk_node.tgCond(d, cond)
            f_node = self.storeNodes(lusFile, nodeWithCondition)
            print kind.runTestGen(f_node)
        else:
            self._log.error("Parsing")


    def generateAndRun(self, lusFile, cond):
        self._log.info("Generating and running test cases")
        progWithTrapProp = self.generateTestCaseConditionFile(lusFile, cond)
        print progWithTrapProp
        kind = KindUtil()
        test_suite = open(lusFile+"_mcdc_test", "w")
        test_cases = ""
        try:
            if progWithTrapProp:
                for prog in progWithTrapProp:
                    try:
                        testXML = kind.runTestGen(prog)
                        test = self.getTestOracle(testXML)
                        spl = " \n".join(x for x in test.split())
                        test_cases += (spl + "\n")
                    except:
                        pass
            test_suite.write(test_cases)
            test_suite.close()
            return test_cases
        except Exception as e:
            self._log.exception("Generating program trap")
            return None


    def generateTestCaseConditionFile(self, lusFile, condFile):
        inputVars = []
        all_tests = {}
        nodeWithCondition = None
        kind = KindUtil()
        progWithTrapProp = []
        if self.parseFile(lusFile):
            self._log.info("Successful parse")
            nodeNames = self.LustreAST.keys()
            mk_node = CcNodes(nodeNames)
            for n,d in self.LustreAST.iteritems():
                if n == "glob":
                    pass
                else:
                    inp = d["input_vars"]
                    out = d["output_vars"]
                    f_cond = open(condFile, "r")
                    all_cond = self.collectInputOutput(inp, out)
                    c_i = 1

                    for c in f_cond.readlines():
                        cl = c.rstrip("\n")
                        newCond = self.makeCondition(cl, all_cond)
                        nodeWithCondition, _, _, _ =  mk_node.tgCond(d, newCond)
                        f_node = self.storeNodes((lusFile+"_"+(str(c_i))), nodeWithCondition)
                        c_i +=1
                        progWithTrapProp.append(f_node)
            return progWithTrapProp
        else:
            self._log.error("Parsing")
            return None

    def collectInputOutput(self, inputs, outputs):
        print "collecting input and output"
        condBool = [inp[0] for inp in inputs if inp[1] == 'bool'] + [out[0] for out in outputs if out[1] == 'bool']
        condInt = [inp[0] for inp in inputs if inp[1] == 'int'] + [out[0] for out in outputs if out[1] == 'int']
        condReal = [inp[0] for inp in inputs if inp[1] == 'real'] + [out[0] for out in outputs if out[1] == 'real']
        print condInt
        print condBool
        b = " and ".join(x for x in condBool)
        i = " and ".join(("("+x+"= 0) or not("+x+" = 0)") for x in condInt)
        r = " and ".join(("("+x+"= 0.0) or not("+x+" = 0.0)") for x in condInt)
        b_cond = "( "+ b + ")"
        i_cond = "( "+ i + ")"
        r_cond = "( "+ r + ")"
        all_cond = {"b": {"cond": b_cond, "var": condBool}, "i": {"cond": i_cond, "var": condInt}, "r": {"cond": r_cond, "var": condReal}}
        return all_cond



    def makeCondition(self, cond, all_cond):
        allGood = False
        for k,v in all_cond.iteritems():
            if v["var"] != []:
                if (v["cond"] not in cond) and v["cond"] != "( )":
                    c = cond + " and " + v["cond"]
                    return c
                else:
                    return cond


# <?xml version="1.0"?>
#   <Results xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance">
#     <testTrace>
#         <Value name="cond_1" type="local" step="0">0</Value>
#         <Value name="cond_1" type="local" step="1">0</Value>
#         <Value name="x" type="input" step="0">0</Value>
#         <Value name="x" type="input" step="1">0</Value>
#         <Value name="reset" type="input" step="0">0</Value>
#         <Value name="reset" type="input" step="1">0</Value>
#         <Value name="y" type="output" step="0">0</Value>
#         <Value name="y" type="output" step="1">0</Value>
#     </testTrace>
# </Results>

    def getTestOracle(self, testCase):
        self._log.info("Getting test oracle")
        print testCase
        bench_out = ""
        try:
            xmldoc = ET.fromstring(testCase)
            test_tag = xmldoc.find("testTrace")
            for test_item in test_tag:
                if test_item.attrib["type"] == "input" and test_item.attrib["step"] == "0":
                    bench_out += test_item.text + " "
            return bench_out
        except Exception as e:
            print e
            print "\t Error in verification"
            return None
