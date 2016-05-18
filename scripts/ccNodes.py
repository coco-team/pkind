class CcNodes(object):
    """
    Creating nodes for verfication of contracts
    """
    def __init__(self, nodeNames):
        self.nodeNames = nodeNames
        return

    def _vars_typ(self, vars_type, div=":"):
        pp = ""
        for var, typ in vars_type.iteritems():
            if div == "=":
                var_ls = var.split()
                lhs = var_ls[0] if len(var_ls)==1 else " , ".join(x for x in var_ls)
                pp += lhs + " = " + typ + ";\n"
            else:
                pp += var + " : " + typ + "; "
        final = pp if div == "=" else pp[:-2]
        return final

    def _io_vars(self, vars):
        pp = ""
        for var in vars:
            pp += var[0] + " : " + var[1] + "; "
        final = pp[:-2]
        return final

    def _local_vars(self, vars_type):
        pp = ""
        for var, typ in vars_type.iteritems():
            pp += var + " : " + typ + "; "
        return "var " +pp

    def _asserts(self, asserts):
        if not asserts:
            return ""
        pp = " "
        for a, v in asserts.iteritems():
            pp += "assert " +  v + "; "
        return pp

    def _makeDefaultProps(self, local_vars, output_vars):
        l = "true "
        o = "true "
        for local, typ in local_vars.iteritems():
            if typ == "bool":
                l += " and " + local
        for out, typ in local_vars.iteritems():
            if typ == "bool":
                o += " and " + out
        props = "--!PROPERTY (" + l  + " and " +  o + ");"
        return props

    def _makeAss(self, ass):
        prop = ""
        observer = ""
        ens_req = ""
        try:
            observer = (ass["observer"])[0] if len(ass["observer"]) == 1 else " and ".join(x for x in ass["observer"])
            prop += "--!PROPERTY : " + observer +  ";\n"
        except Exception as e:
            prop += "\t\t--!PROPERTY : true;\n"
        try:
            if ass["requires"] and ass["ensures"]:
                req = (ass["requires"])[0] if len(ass["requires"]) == 1 else " and ".join(x for x in ass["requires"])
                ens = (ass["ensures"])[0] if len(ass["ensures"]) == 1 else " and ".join(x for x in ass["ensures"])
                ens_req += "("+ req + ") => (" + ens + ")"
                prop += "\t\t--!PROPERTY : " + ens_req +  ";\n"
            elif ass["ensures"]:
                ens = (ass["ensures"])[0] if len(ass["ensures"]) == 1 else " and ".join(x for x in ass["ensures"])
                ens_req += ens
                prop += "\t\t--!PROPERTY : " + ens_req + ";\n"
        except Exception as e:
            pass
        return prop


    def _contracts(self, contract):
        prop = ""
        requires = ""
        req = "true and "
        prop_stream = ""
        stream_it = 1
        prop_var = ""
        prop_dict = {}
        req_prop_stream = ""
        #keep track of the ensures/requires in case we need to include
        prop_rhs = contract["requires"] if 'requires' in contract else []
        try:
            if 'requires' in contract:
                req += "".join(x for x in contract["requires"]) if len(contract["requires"]) == 1\
                    else " and ".join(x for x in contract["requires"])
                requires = "assert ( " + req + " );"
            if 'ensures' in contract:
                for e in contract["ensures"]:
                    prop_name = "P_"+str(stream_it)
                    prop_var +=  prop_name + ":bool;"
                    lhs = self._ensures(e)
                    prop_stream += (prop_name + " = " +  lhs + ";\n")
                    prop_rhs.append(lhs)
                    prop += ("--!PROPERTY : " + prop_name + ";\n")
                    stream_it +=1
                    prop_dict.update({prop_name:lhs})
            if "observer" in contract:
                obs_name = "O_"+str(stream_it)
                prop_var += obs_name + ":bool;"
                obs = contract["observer"][0]
                obs_call = obs.split("(")[0]
                prop_rhs.append(obs_call)
                prop_stream += (obs_name + " = " + obs + ";\n")
                prop += ("--!PROPERTY : " + obs_name + ";\n")
                prop_dict.update({obs_name:obs_call})
            req = "\n" if requires == "true and true" else requires + "\n"
            req_prop_stream += req + prop_stream
        except Exception as e:
            print e
        return prop_var, req_prop_stream, prop, prop_dict, prop_rhs

    def _ensures(self, ens):
        if "pre" in ens:
            return "true -> " + ens
        else:
            return ens



    def ccLustre(self, AST):
        try:
            node_name = AST["node_name"]
            input_vars = self._io_vars(AST["input_vars"])
            output_vars = self._io_vars(AST["output_vars"])
            outSigNum = len(AST["output_vars"]) # Used to know the number of output return
            local_vars = self._local_vars(AST["local_vars"]) if AST["local_vars"] else ""
            streams = self._vars_typ(AST["streams"], "=")
            prop_var, prop_streams, prop, prop_dict, prop_rhs = self._contracts(AST["outSpecs"]) if AST["outSpecs"] else ("", "", "", "", [])
            prop_var_adjusted = ""
            if prop_var:
                prop_var_adjusted = prop_var if local_vars != "" else "var "+prop_var
            asserts = self._asserts(AST["asserts"])
            anyProp = True if prop != "" else False
            extraNodes_Contract = self.extraNodes_contract(prop_rhs)
            extraNodes_Stream = self.extraNodes(AST["streams"])
            extraNodes = list(extraNodes_Contract.union(extraNodes_Stream))
            isMainNode = "--!MAIN : true;" if extraNodes != [] else ""
            node = (""" node %s (%s) returns (%s);
                %s\n
                %s
                let
                    %s
                    %s
                    %s
                    %s
                    %s
                tel
            """) % (node_name, input_vars, output_vars, local_vars, prop_var_adjusted,\
                    streams, asserts, prop_streams, prop, isMainNode)
            return node, prop_dict, extraNodes, anyProp
        except Exception as e:
            print "ccLUSTRE " + str(e)
            return None, None, None


    def mkProp(self, AST):
        try:
            node_name = AST["node_name"]
            input_vars = self._io_vars(AST["input_vars"])
            output_vars = self._io_vars(AST["output_vars"])
            outSigNum = len(AST["output_vars"]) # Used to know the number of output return
            local_vars = self._local_vars(AST["local_vars"]) if AST["local_vars"] else ""
            streams = self._vars_typ(AST["streams"], "=")
            asserts = self._asserts(AST["asserts"])
            prop = "--!PROPERTY: OK;"
            node = (""" node %s (%s) returns (%s);
                %s\n
                let
                    %s
                    %s
                    %s
                tel
            """) % (node_name, input_vars, output_vars, local_vars,\
                    streams, asserts, prop)
            return node
        except Exception as e:
            print "mkProp " + str(e)
            return None

    def mkMutantInv(self, AST, inv):
        try:
            node_name = AST["node_name"]
            input_vars = self._io_vars(AST["input_vars"])
            output_vars = self._io_vars(AST["output_vars"])
            outSigNum = len(AST["output_vars"]) # Used to know the number of output return
            local_vars = self._local_vars(AST["local_vars"]) if AST["local_vars"] else ""
            streams = self._vars_typ(AST["streams"], "=")
            asserts = self._asserts(AST["asserts"])
            node = (""" node %s (%s) returns (%s);
                %s\n
                INV : bool;
                let
                    %s
                    %s
                    %s
                    --!PROPERTY : INV;
                tel
            """) % (node_name, input_vars, output_vars, local_vars,\
                    streams, asserts, inv)
            return node
        except Exception as e:
            print "mkMutantInv " + str(e)
            return None


    def testCondition(self, cond):
        cond_list = cond.split(",")
        condVar = ""
        condStream = ""
        condProp = ""
        i = 1
        for c in cond_list:
            var = "cond_"+str(i)
            condVar += var +":bool;\n"
            i+=1
            condStream += var+" = "+c + ";\n"
            condProp += "--!PROPERTY : " + var + ";\n"
        return condVar, condStream, condProp


    def tgCond(self, AST, cond):
        try:
            node_name = AST["node_name"]
            input_vars = self._io_vars(AST["input_vars"])
            output_vars = self._io_vars(AST["output_vars"])
            outSigNum = len(AST["output_vars"]) # Used to know the number of output return
            local_vars = self._local_vars(AST["local_vars"]) if AST["local_vars"] else ""
            streams = self._vars_typ(AST["streams"], "=")
            prop_var, prop_streams, prop, prop_dict, prop_rhs = self._contracts(AST["outSpecs"]) if AST["outSpecs"] else ("", "", "", "", [])
            prop_var_adjusted = prop_var if local_vars != "" else "var "+prop_var
            asserts = self._asserts(AST["asserts"])
            anyProp = True if prop != "" else False
            extraNodes_Contract = self.extraNodes_contract(prop_rhs)
            extraNodes_Stream = self.extraNodes(AST["streams"])
            extraNodes = list(extraNodes_Contract.union(extraNodes_Stream))
            isMainNode = "--!MAIN : true;" if extraNodes != [] else ""
            condVar, condStream, condProp = self.testCondition(cond)
            node = (""" node %s (%s) returns (%s);
                %s
                %s
                %s\n
                let
                    %s
                    %s
                    %s
                    %s
                    %s
                    %s
                    %s
                tel
            """) % (node_name, input_vars, output_vars, local_vars, prop_var_adjusted,\
                    condVar, streams, asserts, prop_streams, prop, condStream, condProp, isMainNode)
            return node, prop_dict, extraNodes, anyProp
        except Exception as e:
            print " tgCond " + str(e)
            return None, None, None


    def invTestCases(self, invariants):
        invs =  invariants.split("\n")
        inv_vars = ""
        inv_defs = ""
        inv_prop = ""
        i = 10;
        for inv in invs:
            if inv != '':
                inv_vars += "PT_"+str(i)+ " : bool; "
                inv_prop += "--!PROPERTY : PT_"+str(i)+" ;\n"
                inv_defs += inv+"\n"
                i += 1
        return inv_vars, inv_defs, inv_prop



    def tgLustre(self, AST, invariants):
        try:
            inv_vars, inv_defs, inv_prop = self.invTestCases(invariants)
            node_name = AST["node_name"]
            input_vars = self._io_vars(AST["input_vars"])
            output_vars = self._io_vars(AST["output_vars"])
            outSigNum = len(AST["output_vars"]) # Used to know the number of output return
            local_vars = self._local_vars(AST["local_vars"]) if AST["local_vars"] else ""
            streams = self._vars_typ(AST["streams"], "=")
            prop_var, prop_streams, prop, prop_dict, prop_rhs = self._contracts(AST["outSpecs"]) if AST["outSpecs"] else ("", "", "", "", [])
            prop_var_adjusted = prop_var if local_vars != "" else "var "+prop_var
            asserts = self._asserts(AST["asserts"])
            anyProp = True if prop != "" else False
            extraNodes_Contract = self.extraNodes_contract(prop_rhs)
            extraNodes_Stream = self.extraNodes(AST["streams"])
            extraNodes = list(extraNodes_Contract.union(extraNodes_Stream))
            isMainNode = "--!MAIN : true;" if extraNodes != [] else ""
            node = (""" node %s (%s) returns (%s);
                %s\n
                %s\n
                %s
                let
                    %s
                    %s
                    %s
                    %s
                    %s
                    %s
                    %s
                tel
            """) % (node_name, input_vars, output_vars, local_vars, prop_var_adjusted, inv_vars,\
                    streams, asserts, prop_streams, prop, inv_defs, isMainNode, inv_prop)
            return node, prop_dict, extraNodes, anyProp
        except Exception as e:
            print "ccLUSTRE " + str(e)
            return None, None, None

    def extraNodes(self, vars_type):
        nodes = []
        for rhs, lhs in vars_type.iteritems():
            for node in self.nodeNames:
                if node in lhs:
                    nodes.append(node)
        return set(nodes)

    def extraNodes_contract(self, prop_rhs):
        nodes = []
        for node in self.nodeNames:
            if node in " ".join(x for x in prop_rhs):
                nodes.append(node)
        return set(nodes)
