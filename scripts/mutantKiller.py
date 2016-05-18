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


class MutantKiller(object):
    def __init__(self):
        self._log = LoggingManager.get_logger(__name__)
        self.composer = NodeComposer()
        return

    def parseFile(self, lusFile):
        self._log.debug("Parsing Lustre file: %s" % lusFile)
        parser = LParser()
        with open(lusFile, 'r') as f:
            try:
                self.LustreAST= parser.parse(f.read())
                self._log.debug(parser.ppAST(self.LustreAST))
                return True
            except ParseException, err:
                self._log.exception(str(err))
                return False

    def run(self, mutantFile, inv):
        """ MAIN FUNCTION """
        self._log.debug("Running : " + mutantFile)
        kind = KindUtil()
        mutant_inv = self.mkMutantwithInvariant(mutantFile, inv)
        if mutant_inv:
            self._log.info( mutantFile + " ... OK")
            try:
                testXML = kind.runTestGen(mutant_inv)
                return testXML
            except Exception as e:
                self._log.exception(str(e))
        else:
            self._log.error(mutantFile + " ... NOT OK")
            return None

    def generateInv(self, lusFile):
        """ GENERATE INVARIANT FOR THE ORIGINAL LUSTRE FILE"""
        self._log.debug("Generating invariants")
        kind = KindUtil()
        try:
            if self.parseFile(lusFile):
                self._log.debug("Successful parse")
                nodeNames = self.LustreAST.keys()
                mk_node = CcNodes(nodeNames)
                for n,d in self.LustreAST.iteritems():
                    if n == "glob":
                        pass
                    else:
                        lustre_with_prop = mk_node.mkProp(d)
                        f_prop = lusFile+"_PROP"
                        if os.path.isfile(f_prop):
                            self._log.warning("ALREADY TESTED")
                            return None
                        else:
                            with open(f_prop, "w") as f:
                                f.write(lustre_with_prop)
                            inv = kind.mkInv(f_prop)
                            return inv
            else:
                self._log.error("Parsing")
                return None
        except Exception as e:
            self._log.exception(str(e))
            return None


    def mkMutantwithInvariant(self, mutant, inv):
        self._log.debug("Generating mutant with invariant")
        kind = KindUtil()
        m_file = open(mutant+"_INV", "w")
        try:
            if self.parseFile(mutant):
                self._log.debug("Successful parse")
                nodeNames = self.LustreAST.keys()
                mk_node = CcNodes(nodeNames)
                for n,d in self.LustreAST.iteritems():
                    if n == "glob":
                        pass
                    else:
                        inp = d["input_vars"]
                        out = d["output_vars"]
                        all_cond = self.collectInputOutput(inp, out)
                        newCond = self.makeCondition(inv, all_cond)
                        mutant_inv =  mk_node.mkMutantInv(d, newCond)
                        m_file.write(mutant_inv)
                        m_file.close()
                        return mutant+"_INV"
            else:
                self._log.error("Parsing")
                return None
        except Exception as e:
            self._log.exception("Generating program trap")
            return None

    def collectInputOutput(self, inputs, outputs):
        condBool = [inp[0] for inp in inputs if inp[1] == 'bool'] + [out[0] for out in outputs if out[1] == 'bool']
        condInt = [inp[0] for inp in inputs if inp[1] == 'int'] + [out[0] for out in outputs if out[1] == 'int']
        condReal = [inp[0] for inp in inputs if inp[1] == 'real'] + [out[0] for out in outputs if out[1] == 'real']
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
                    return c + "));"
                else:
                    return cond + "));"

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
