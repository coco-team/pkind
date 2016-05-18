from LogManager import LoggingManager
from lustreParser import LParser
from pyparsing import ParseException
from nodeDecomposer import NodeComposer

class LustreTransform(object):

	def __init__(self):
		self._log = LoggingManager.get_logger(__name__)
		return


	def _transform(self,lusFile):
		self._log.info("Transforming %s", str(lusFile))
		composer = NodeComposer()
		try:
			componentNodes = composer.decompose(lusFile)
			print componentNodes
		except Exception as e:
			self._log.exception(str(e))





