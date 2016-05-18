import time
import os,subprocess,sys
import multiprocessing as mp
from Queue import Queue
from threading import Thread
from LogManager import LoggingManager
import threading
import shutil


class KindUtil(object):
    def __init__(self):
        self._log = LoggingManager.get_logger(__name__)
        return

    def runLsimplify(self, lusFile):
        self._log.debug("Running Lsimplify")
        cmd = ["lsimplify", "-s", "-nm", lusFile]
        p = subprocess.Popen(cmd, shell=False, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        result, _ = p.communicate()
        return result

    def mkInv(self, lusFile, timeout=30):
        self._log.debug("Invariant generation for test cases .. . " + str(lusFile))
        cmd = ["kind-inv", "-inv_int", "-inv_bool", "-rm_trivial_inv", lusFile]
        p = subprocess.Popen(cmd, shell=False, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        while timeout > 0:
            if p.poll() is not None:
                result, _ = p.communicate()
                return result
            time.sleep(0.1)
            timeout -= 0.1
        else:
            try:
                p.kill()
            except OSError as e:
                if e.errno != 3:
                    raise
        return None

    def runTestGen(self, lusFile, timeout=10):
        self._log.debug("Test cases generation ... " + str(lusFile))
        cmd = ["pkind", "-tg", lusFile]
        p = subprocess.Popen(cmd, shell=False, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        while timeout > 0:
            if p.poll() is not None:
                result, _ = p.communicate()
                return result
            time.sleep(0.1)
            timeout -= 0.1
        else:
            try:
                p.kill()
            except OSError as e:
                if e.errno != 3:
                    raise
        return None

    def runCompiler(self, lusFile, node):
        self._log.info("Compiling ... " + str(lusFile))
        current_dir = os.getcwd()
        d = os.path.dirname(lusFile)
        f_name = os.path.splitext(os.path.basename(lusFile))[0]
        c = f_name+".c"
        h = f_name+".h"
        cFile = current_dir+os.sep+c
        hFile = current_dir+os.sep+h
        cmd = ["lustrec", "-d", d, "-node", node, lusFile]
        p = subprocess.Popen(cmd, shell=False, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        shutil.copy(cFile, d)
        shutil.copy(hFile, d)
        result, _ = p.communicate()
        currenCfile = d+os.sep+c
        return result, currenCfile


    def runCCompiler(self, place, cFile):
        self._log.info("Compiling ... " + str(cFile))
        outFile = (cFile.split("."))[0]
        io_frontend = place+os.sep+"io_frontend.o"
        cmd = ["gcc", "-o", outFile, io_frontend, cFile]
        p = subprocess.Popen(cmd, shell=False, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        result, _ = p.communicate()
        return result, outFile

    def runTestCases(self, tc, prog):
        self._log.info("Running test case " + str(tc))
        cmd = [prog, "<", tc]
        p = subprocess.Popen(cmd, shell=False, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        result, _ = p.communicate()
        return result




class PkindJobs(threading.Thread):

    _active_tasks = []

    def __init__(self):
        self._log = LoggingManager.get_logger(__name__)
        return

    @property
    def all_tasks_done(self):
        return len(self.active_tasks) <=0

    @property
    def active_tasks(self):
        return self._active_tasks


    def GetInvariants(self, inv):
        self._log.exception("GetInvariants is NOT overridden")
        pass

    def PropertyResult(self, propResult):
        self._log.exception("Property result is NOT overridden")
        self._propDone = True
        pass

    def WaitAllTasksDone(self, timeout=None):
        start_time = time.time()
        while self.all_tasks_done is False and True if timeout is None else start_time + timeout > time.time():
            time.sleep(1)

    @classmethod
    def _add_task(cls, task):
        cls._active_tasks.append(task)

    @classmethod
    def _remove_task(cls, task):
        cls._active_tasks.remove(task)

    def runJobs(self, job_id, node_name, job, timeout):
        self._log.info("Running Pkind : %s", job_id)
        th = PkindThread(self, job_id, node_name, job, timeout)
        self._add_task(th)
        th.start()
        th.join(timeout)
        if th.is_alive():
            self._log.info("TIMEOUT for : %s" % th.getName())
            th.p.terminate()
            th.join()




class PkindThread(threading.Thread):

    def __init__(self, pkind, job_id, node_name, cmd, timeout):
        self.cmd = cmd
        self.pkind = pkind
        self.timeout = timeout
        self.node_name = node_name
        self.p = None
        super(PkindThread, self).__init__()
        self.setName(job_id)
        return

    def task_done(self):
        PkindJobs._remove_task(self)


    def run(self):
        self.p = subprocess.Popen(self.cmd, shell=False, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        result, stderr = self.p.communicate()
        if "</Property>" in result:
            self.pkind.PropertyResult({self.node_name : result})
        elif "error" in result+stderr:
            error = "<Error>\n"
            error += "<stdout>\n" + str(result) + "</stdout>\n"
            error += "<stderr>\n"+ str(stderr) + "</stderr>\n"
            error += "</Error>"
            self.pkind.PropertyResult({self.node_name: error})
        return
