import argparse
import textwrap
import json
import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d import Axes3D

def _onlyz3(json_file):
    jf = json.loads(open(json_file).read())
    solved_runtime = []
    solved_bench = []
    unsolved = []
    a = 0
    minim = 0.0000
    maximum = 0.0
    try:
        for k,d in jf.iteritems():
            print k
            a += 1
            if (d["Z3"])["RESULT"] == "valid":
                run = (d["Z3"])["RUNTIME"]
                solved_runtime.append(run)
                if minim > run:
                    minim = run
                if run > maximum:
                    maximum = run
                solved_bench.append(k)
            if (d["Z3"])["RESULT"] == "timeout":
                unsolved.append(k)
        print "ALL " + str(a)
        print "SOLVED " + str(len(solved_bench))
        print "UNSOLVED " + str(len(unsolved))
        print "MIN " + str(minim)
        print "MAX " + str(maximum)
    except:
        print "ALL " + str(a)
        print "SOLVED " + str(len(solved_bench))
        print "UNSOLVED " + str(len(unsolved))
        print "MIN " + str(minim)
        print "MAX " + str(maximum)

def _single_vs_modular(json_file):
    jf = json.loads(open(json_file).read())
    csvName = (json_file.split("."))[0]
    csvF = open((csvName+".csv"), 'w')
    csv = "benchmark, single_result, single_runtime, modular_result, modular_runtime\n"
    single_encoding = []
    modular_encoding = []
    for k,d in jf.iteritems():
        print "Processing .... " + str(k)
        single_runtime = (d["SINGLE"])["RUNTIME"] if str((d["SINGLE"])["RUNTIME"]) != "timeout" else 100.0
        single_encoding.append(single_runtime)
        modular_runtime =  (d["MODULAR"])["RUNTIME"] if str((d["MODULAR"])["RUNTIME"]) != "timeout" else 100.0
        modular_encoding.append(modular_runtime)
        single_result = (d["SINGLE"])["RESULT"]
        modular_result = (d["MODULAR"])["RESULT"]
        csv += k + "," + single_result + "," + str(single_runtime) + "," + modular_result + "," + str(modular_runtime) + "\n"
    for i,j in zip(single_encoding, modular_encoding):
        print str(i) + " ... " + str(j)
    csvF.write(csv)
    csvF.close()
    print "Plotting ..."
    fig = plt.figure()
    valid = fig.add_subplot(1,1,1)
    valid.plot(single_encoding, modular_encoding, 'ro', color='blue', lw=2)
    valid.plot([0.01, 100.0], [0.01, 100.0], 'k-', c='red', lw=2)
    valid.set_yscale('log')
    valid.set_xscale('log')
    valid.set_xlabel('Single Encoding')
    valid.set_ylabel('Modular Encoding')
    plt.show()
    #plt.savefig('pkind_z3_valid_diff.png')
    return

def _makeCSV(json_file, csvName):
    jf = json.loads(open(json_file).read())
    csvF = open((csvName+".csv"), 'w')
    benchWithData = {}
    csv = "benchmark, pkind_result, pkind_runtime, pkind_k, z3_result, z3_runtime, z3_depth\n"
    for k,d in jf.iteritems():
        for k,d in jf.iteritems():
            if d["PKIND-INV"] is not None  or d["Z3"] is not None:
                benchWithData.update({k:d})
    for k,d in benchWithData.iteritems():
        try:
            csv += k + ", " + (d["PKIND-INV"])["RESULT"] + ", " +  (d["PKIND-INV"])["RUNTIME"] + ", "\
                    + (d["PKIND-INV"])["K"] + ", " +  (d["Z3"])["RESULT"] + ", " + (d["Z3"])["RUNTIME"]\
                    + ", " + (d["Z3"])["PDR-DEPTH"] + "\n"
        except Exception as e:
            print str(e)
            csv += k + ", Nan, Nan, Nan, Nan, Nan, Nan\n"
    print csv
    csvF.write(csv)
    csvF.close()

def _analysis(json_file):
    jf = json.loads(open(json_file).read())
    benchWithData = {}
    invalidBench = {}
    validBench = {}
    validInvBench = {}
    validWithInvCorrect = {}
    onlyZ3 = {}
    unknown = {}
    for k,d in jf.iteritems():
        if d["PKIND-INV"] is not None or d["PKIND"] is not None or d["Z3"] is not None:
            benchWithData.update({k:d})
    print "Bench with data " + str(len(benchWithData))
    for k,d in benchWithData.iteritems():
        if (d["PKIND-INV"])["RESULT"] != "timeout":
            validWithInvCorrect.update({k:d})
    print "Correct bench with inv  " + str(len(validWithInvCorrect))

def _analysisK2(json_file):
    jf = json.loads(open(json_file).read())
    kind2 = []
    z3 = []
    kindinv = []
    pkind = []
    kind2Valid = 0
    z3Valid = 0
    pkindValid = 0
    pkind_not_z3 = [] # solved by pkind and not by z3
    z3_not_pkind = [] # solved by z3 and not pkind
    for k,d in jf.iteritems():
        try:
            if str((d["PKIND-INV"])["RUNTIME"]) != "timeout":
                pkind.append((d["PKIND-INV"])["RUNTIME"])
                pkindValid += 1
            else:
                pkind.append('100')
        except:
            pkind.append('100')
        try:
            if str((d["KIND2"])["RUNTIME"]) != "timeout":
                kind2.append((d["KIND2"])["RUNTIME"])
                kind2Valid += 1
            else:
                kind2.append('20')
        except:
            kind2.append('100')
        try:
            if str((d["Z3"])["RUNTIME"]) != "timeout":
                z3.append((d["Z3"])["RUNTIME"])
                z3Valid += 1
            else:
                z3.append('100')
        except:
            z3.append('100')

        if str((d["PKIND-INV"])["RUNTIME"]) != "timeout" and str((d["Z3"])["RUNTIME"]) == "timeout":
                pkind_not_z3.append(k)
        elif str((d["PKIND-INV"])["RUNTIME"]) == "timeout" and str((d["Z3"])["RUNTIME"]) != "timeout":
                z3_not_pkind.append(k)


    print "--> All Benchmarks: " + str(len(jf))
    print "--> Solved by Kind2  " + str(kind2Valid)
    print "--> Solved by Z3  " + str(z3Valid)
    print "--> Solved by Pkind  " + str(pkindValid)
    print "--> Solved by Pkind and Not by Z3 " + str(len(pkind_not_z3))
    print pkind_not_z3
    print "============"
    print "--> Solved by Z3 and Not by Pkind " + str(len(z3_not_pkind))
    print z3_not_pkind
    print "==========="
    fig = plt.figure()
    valid = fig.add_subplot(1,1,1)

    valid.plot(pkind, z3, 'ro', color='blue', lw=2)
    valid.plot([0.01, 100], [0.01, 100], 'k-', c='red', lw=2)
    valid.set_yscale('log')
    valid.set_xscale('log')
    valid.set_xlabel('PKIND')
    valid.set_ylabel('Z3')
    plt.show()
    #plt.savefig('pkind_z3_valid_diff.png')
    return


# def _analysis(json_file):
#     jf = json.loads(open(json_file).read())
#     benchWithData = {}
#     invalidBench = {}
#     validBench = {}
#     validInvBench = {}
#     validNoCompBench = {}
#     onlyZ3 = {}
#     unknown = {}
#     for k,d in jf.iteritems():
#         if d["PKIND-INV"] is not None or d["PKIND"] is not None or d["Z3"] is not None:
#             benchWithData.update({k:d})
#     for k, d in benchWithData.iteritems():
#         try:
#             if (d["PKIND"])["RESULT"] == "falsifiable" and (d["Z3"])["RESULT"] == "falsifiable":
#                 invalidBench.update({k:d})
#             if (d["PKIND"])["RESULT"] == "valid" and (d["Z3"])["RESULT"] == "valid":
#                 validBench.update({k:d})
#             if (d["PKIND-INV"])["RESULT"] == "valid" and (d["Z3"])["RESULT"] == "valid":
#                 validInvBench.update({k:d})
#             if (d["PKIND-INV"])["RESULT"] == "timeout" and (d["Z3"])["RESULT"] == "valid":
#                 onlyZ3.update({k:d})
#             if (d["PKIND-INV"])["RESULT"] == "timeout" and (d["Z3"])["RESULT"] == "timeout":
#                 unknown.update({k:d})
#             if (d["PKIND-NO-COMP"])["RESULT"] == "valid" and (d["Z3"])["RESULT"] == "valid":
#                 validNoCompBench.update({k:d})
#         except:
#             pass

    # plot(benchWithData)
    # print "==============="
    # print "\t Only Solved by Z3:"
    # print onlyZ3.keys()

# def plot(validInvBench):
#     print "plotting ... "
#     validRuntime = []
#     hornRuntime = []
#     notSolvedZ3 = 0
#     notSolvedPkind = 0
#     for bench, result in validInvBench.iteritems():
#         try:
#             res_pkind = (result["PKIND-INV"])["RESULT"]
#             res_z3 = (result["Z3"])["RESULT"]
#             if str((result["PKIND-INV"])["RUNTIME"]) == "timeout":
#                 validRuntime.append('100.0')
#                 notSolvedPkind += 1
#             else:
#                 validRuntime.append((result["PKIND-INV"])["RUNTIME"])
#             if (result["Z3"])["RUNTIME"] == "timeout":
#                 hornRuntime.append('100.0')
#                 notSolvedZ3 += 1
#             else:
#                 hornRuntime.append((result["Z3"])["RUNTIME"])
#         except:
#             pass
#     print "Not solved by Z3 ... " + str(notSolvedZ3)
#     print "Not solved by Pkind ... " + str(notSolvedPkind)
#     print hornRuntime
#     print validRuntime
#     fig = plt.figure()
#     valid = fig.add_subplot(1,1,1)
#     valid.plot(validRuntime, hornRuntime, 'ro', color='blue', lw=2)
#     valid.set_ylim(0,0.3)
#     valid.set_xlim(0,0.3)
#     plt.ylabel('Z3 - PDR')
#     plt.xlabel('PKIND With Invariants')
#     plt.show()
#     #plt.savefig('pkdin_no_comp.png')
#     return

# def plot(validBench, validInvBench, validNoCompBench):
#     print "plotting ... "
#     validRuntime = []
#     validInvRuntime = []
#     validNoCompRuntime = []
#     hornRuntime = []
#     for bench, result in validBench.iteritems():
#         try:
#             res_pkind = (result["PKIND"])["RESULT"]
#             res_z3 = (result["Z3"])["RESULT"]
#             validRuntime.append((result["PKIND"])["RUNTIME"])
#             hornRuntime.append((result["Z3"])["RUNTIME"])
#         except:
#             pass
#     for bench, result in validInvBench.iteritems():
#         try:
#             validNoCompRuntime.append((result["PKIND-INV"])["RUNTIME"])
#         except:
#             pass
#     for bench, result in validNoCompBench.iteritems():
#         try:
#             res_pkind = (result["PKIND"])["RESULT"]
#             res_z3 = (result["Z3"])["RESULT"]
#             validInvRuntime.append((result["PKIND-NO-COMP"])["RUNTIME"])
#         except:
#             pass
#     fig = plt.figure()
#     valid = fig.add_subplot(1,1,1)
#     valid.plot(validNoCompRuntime, hornRuntime, 'ro', color='blue', lw=2)
#     valid.set_ylim(0,0.3)
#     valid.set_xlim(0,0.3)
#     # validInv = fig.add_subplot(3,2,1)
#     # validInv.plot(validInvRuntime, hornRuntime, 'ro', color='blue', lw=2)
#     # validInv.set_ylim(0,0.3)
#     # validInv.set_xlim(0,0.3)
#     # validNoComp = fig.add_subplot(3,3,3)
#     # validNoComp.plot(validNoCompRuntime, hornRuntime, 'ro', color='blue', lw=2)
#     # validNoComp.set_ylim(0,0.3)
#     # validNoComp.set_xlim(0,0.3)
#     #plt.show()
#     # ax.savefig((tag + '.png'))
#     plt.ylabel('Z3 - PDR')
#     plt.xlabel('PKIND')
#     #plt.show()
#     plt.savefig('pkdin_no_comp.png')
#     return


if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        prog='Analysis',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        description=textwrap.dedent('''\
                  Analysis
            --------------------------------
            '''))
    parser.add_argument('-j', '--json', required=True, dest="file" )
    parser.add_argument('-z3', '--onlyz3', required=False, dest="onlyz3", action = "store_true")
    parser.add_argument('-csv', '--csv', required=False, dest="csv")
    args = parser.parse_args()
    f = args.file
    onlyz3 = args.onlyz3
    csv = args.csv
    try:
        if onlyz3:
            _single_vs_modular(f)
        elif csv:
            _makeCSV(f,csv)
        else:
            _analysisK2(f)
    except Exception as e:
        print str(e)
