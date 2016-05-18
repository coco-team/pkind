import argparse
import textwrap
from LogManager import LoggingManager
import json
import glob
import os
from mutantKiller import MutantKiller

_log = LoggingManager.get_logger(__name__)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        prog="Benchmarking validating compiler",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        description=textwrap.dedent('''\
            * Benchmarking validating compiler
            ---------------------------------------------------
            '''))
    parser.add_argument('-v', '--version', action='version', version=('%(prog)s 0.1'))
    parser.add_argument('-d', '--dir', dest="bench", required=False)
    parser.add_argument('-i', '--inc', dest="inc", required=False)
    parser.add_argument('-l', '--list', dest="l", required=False)
    args = parser.parse_args()
    bench_dir = args.bench
    inc = args.inc
    list_bench = args.l
    try:
        if bench_dir:
            original_lus = (glob.glob(bench_dir+os.sep+"*top*"))[0]
            mutants_dir = bench_dir + os.sep + "mutants" + os.sep
            mutants_list = glob.glob(mutants_dir+"*.lus")
            m_killer = MutantKiller()
            new_tests = bench_dir + os.sep + "new_tests" + os.sep
            if not os.path.exists(new_tests):
                os.makedirs(new_tests)
            total_bench = len(mutants_list)
            ok = 0
            not_ok = 0
            for m in mutants_list:
                m_name = os.path.basename(m)
                test = m_killer.run(original_lus, m)
                if test:
                    ok += 1
                    with open(new_tests + m_name + "_NEW_TEST", "w") as f:
                        f.write(test)
                else:
                    not_ok += 1
            summary = ("""
            \t  ---- SUMMARY ----
            \t TOTAL MUTANTS : %s\n
            \t KILLED MUTANT : %s\n
            \t ALIVE MUTANT  : %s\n
            -----------------
            """, str(total_bench), str(ok), str(not_ok))
            print summary
        elif list_bench:
            f_bench = glob.glob(list_bench+"*")
            summary_f = open("summary", "w")
            summary = {}
            for bench in f_bench:
                abs_bench = os.path.abspath(bench)
		bench_name = os.path.basename(abs_bench)
                original_lus = (glob.glob(abs_bench+os.sep+"*top*"))[0]
		mutants_dir = abs_bench + os.sep + "mutants" + os.sep
		mutants_list = glob.glob(mutants_dir+"*.lus")
		m_killer = MutantKiller()
                new_tests = abs_bench + os.sep + "new_tests" + os.sep
                if not os.path.exists(new_tests):
                    os.makedirs(new_tests)
                total_bench = len(mutants_list)
                ok = 0
                not_ok = 0
                inv = m_killer.generateInv(original_lus)
                if inv and "INV" in inv:
                    _log.info("Invariant Generation: OK")
                    for m in mutants_list:
                        m_name = os.path.basename(m)
                        test = m_killer.run(m, inv)
                        if test:
                            ok += 1
                            with open(new_tests + m_name + "_NEW_TEST", "w") as f:
                                f.write(test)
                        else:
                            not_ok += 1
                    print "INV_TEST RESULT:\t", bench_name, total_bench, ok, not_ok
                    summary.update({bench_name:{"success": str(ok), "total": str(total_bench)}})
                    # summary = ("""
                    # \t  ---- SUMMARY ----
                    # \t BENCH NAME    : %s\n
                    # \t TOTAL MUTANTS : %s\n
                    # \t KILLED MUTANT : %s\n
                    # \t ALIVE MUTANT  : %s\n
                    # -----------------
                    # """, bench_name, str(total_bench), str(ok), str(not_ok))
                    print summary
                    summary_f.write(str(summary))
                else:
                    _log.error("Invariant Generation: NOT OK")
            summary_f.close()
        else:
            _log.error("Wrong option type python horn.py -h")
    except Exception as e:
        _log.exception(str(e))
