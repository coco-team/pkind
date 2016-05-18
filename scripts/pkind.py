import argparse
import textwrap
from LogManager import LoggingManager
from nodeDecomposer import NodeSynth
from lustreTransform import LustreTransform
from traceExecutor import TestGeneration
from randomTests import RandomTestGeneration
from mutantKiller import MutantKiller
import shutil


def check_bins(program):
    import os
    def is_exe(fpath):
        return os.path.isfile(fpath) and os.access(fpath, os.X_OK)

    fpath, fname = os.path.split(program)
    if fpath:
        if is_exe(program):
            return program
    else:
        for path in os.environ["PATH"].split(os.pathsep):
            path = path.strip('"')
            exe_file = os.path.join(path, program)
            if is_exe(exe_file):
                return exe_file
    return None


if __name__ == "__main__":
    _log = LoggingManager.get_logger(__name__)
    parser = argparse.ArgumentParser(
        prog='PKIND Scripts',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        description=textwrap.dedent('''\
                  PKIND Scripts for:
                       * Automated test case generation
                       * Automated test case executor
                       * Automated generator of mutant killer

            ---------------------------------------------------
            '''))
    parser.add_argument('-pkind', '--pkind_option', default="",  dest="pkind_option")
    parser.add_argument('-v', '--version', action='version', version=('%(prog)s 0.1'))
    parser.add_argument('-f', '--file', required=True, dest="lustre_file" )
    parser.add_argument('-ef', '--eacs_file', required=False,  dest="eacsl_file" )
    parser.add_argument('-t', '--timeout', required=False, type=int, default=10, dest="timeout" )
    parser.add_argument('-cc', '--checkContracts', required=False, dest="contracts" , action="store_true", default= False)
    parser.add_argument('-l', '--lustreTransform', required=False, dest="transform", action="store_true", default=False )
    parser.add_argument('-tg', '--testGen', required=False, dest='testGen' , action = "store_true")
    parser.add_argument('-c', '--cond', required=False, dest='cond')
    parser.add_argument('-r', '--randTest', required=False, dest='randTest', action = "store_true", default = False)
    parser.add_argument('-d', '--depth', required=False, type=int, default=5, dest="depth")
    parser.add_argument('-n', '--node', required=False, dest="node")
    parser.add_argument('-cf', '--cond_file', required=False, dest="cond_file")
    parser.add_argument('-inv', '--inv_file', required=False, action = "store_true", dest="inv_test")
    parser.add_argument('-mu', '--mutant', required=False,  dest="mutant")

    args = parser.parse_args()
    pkind_option = args.pkind_option
    lustre_file = args.lustre_file
    timeout = args.timeout
    contracts = args.contracts
    transform = args.transform
    testGen = args.testGen
    cond = args.cond
    condFile = args.cond_file
    randTest = args.randTest
    depth = args.depth
    node = args.node
    eacsl = args.eacsl_file
    inv_test = args.inv_test
    mutant = args.mutant

    if not check_bins("pkind"):
        _log.error("First install PKIND")

    if testGen:
        _log.info("Generating test cases")

        ts = TestGeneration()
        try:
            ts.generateTestCase(lustre_file)
        except Exception as e:
            _log.exception(str(e))
    elif contracts:
        _log.info("Checking contracts")
        sa = NodeSynth(contracts, pkind_option, lustre_file, timeout)
        trans = LustreTransform()
        try:
            print(sa.run())
        except Exception as e:
            _log.exception(str(e))
    elif transform:
        _log.info("Transform Lustre program")
        try:
            trans._transform(lustre_file)
        except Exception as e:
            _log.exception(str(e))
    elif randTest:
        if not node:
            _log.error("specify main node to be tested")
        else:
            _log.info("Random test generation")
            rand = RandomTestGeneration()
            try:
                _log.info("Generate random test cases")
                tests = rand.randomTestGen(lustre_file,depth, node)
                if eacsl:
                    _log.info("Running test cases")
                    rand.runTestCases(tests, eacsl)
            except Exception as e:
                _log.exception(str(e))
    elif cond is not None or condFile is not None:
        _log.info("Generate test cases with conditions")
        rand = RandomTestGeneration()
        try:
            if cond:
                rand.generateTestCaseCondition(lustre_file, cond)
            elif condFile:
                rand.generateAndRun(lustre_file, condFile)
        except Exception as e:
                _log.exception(str(e))
    elif inv_test:
        try:
            _log.info("Mutant Killer")
            if not mutant:
                _log.error("Provide a mutated program")
            else:
                m_killer = MutantKiller()
                m_killer.run(lustre_file, mutant)
        except Exception as e:
            _log.exception("Generating Mutant Killer\n " + str(e))
    else:
        _log.error("No option specified")
