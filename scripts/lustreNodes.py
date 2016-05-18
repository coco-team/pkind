class BuildLusteNode(object):
    
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

    def _contractsG(self, contract):
        prop = ""
        requires = "true and "
        prop_stream = ""
        stream_it = 1
        prop_var = ""
        prop_dict = {}
        prop_rhs = contract["requires"] if 'requires' in contract else []#keep track of the ensures/requires in case we need to include 
        try:
            if 'requires' in contract:
                requires = "".join(x for x in contract["requires"]) if len(contract["requires"]) == 1\
                    else " and ".join(x for x in contract["requires"])
            else:
                requires += "true"
            if 'ensures' in contract: 
                for e in contract["ensures"]:
                    prop_name = "P_"+str(stream_it)
                    prop_var +=  prop_name + ":bool;"
                    lhs = self._ensures(e)
                    lhs_fml =  lhs if requires == "true and true" else ("(" + requires + ") => " + lhs)
                    prop_stream += (prop_name + " = " +  lhs_fml + ";\n")
                    prop_rhs.append(lhs)
                    prop += ("--!PROPERTY : " + prop_name + ";\n")
                    stream_it +=1
                    prop_dict.update({prop_name:self._ensures(e)})                
        except Exception as e:
            pass
        return prop_var, prop_stream, prop, prop_dict, prop_rhs

    def _contracts(self, contract):
        prop = ""
        requires = ""
        req = "true and "
        prop_stream = ""
        stream_it = 1
        prop_var = ""
        prop_dict = {}
        req_prop_stream = ""
        prop_rhs = contract["requires"] if 'requires' in contract else []#keep track of the ensures/requires in case we need to include 
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
                obs_vars_list = len((obs.split("(")[1]).split(","))
                obs_true = " , ".join(x for x in ["true" for x in range(obs_vars_list)])
                prop_rhs.append(obs_call)
                prop_stream += (obs_name + " = " + obs + " = ( " + obs_true + " );\n")
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

    def kindLustre(self, AST):
        try:
            node_name = AST["node_name"]
            input_vars = self._vars_typ(AST["input_vars"])
            output_vars = self._vars_typ(AST["output_vars"])
            local_vars = self._local_vars(AST["local_vars"]) if AST["local_vars"] else ""
            streams = self._vars_typ(AST["streams"], "=")
            prop = self._makeAss(AST["outSpecs"]) if AST["outSpecs"] else ""
            asserts = self._asserts(AST["asserts"])
            node = (""" node %s (%s) returns (%s); 
                %s
                let
                    %s
                    %s
                    %s
                tel
            """) % (node_name, input_vars, output_vars, local_vars, streams, asserts, prop)
            return node
        except Exception as e:
            print str(e)
            
    def ccLustre(self, AST):
        try:
            node_name = AST["node_name"]
            input_vars = self._io_vars(AST["input_vars"])
            output_vars = self._io_vars(AST["output_vars"])
            local_vars = self._local_vars(AST["local_vars"]) if AST["local_vars"] else ""
            streams = self._vars_typ(AST["streams"], "=")
            prop_var, prop_streams, prop, prop_dict, prop_rhs = self._contracts(AST["outSpecs"]) if AST["outSpecs"] else ("", "", "", "", [])
            prop_var_adjusted = prop_var if local_vars != "" else "var "+prop_var
            asserts = self._asserts(AST["asserts"])
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
            print node
            return node, prop_dict, extraNodes

        except Exception as e:
            print "ccLUSTRE " + str(e)
            return None, None, None

    def tgLustre(self, AST, invariants):
        try:
            node_name = AST["node_name"]
            input_vars = self._io_vars(AST["input_vars"])
            output_vars = self._io_vars(AST["output_vars"])
            local_vars = self._local_vars(AST["local_vars"]) if AST["local_vars"] else ""
            streams = self._vars_typ(AST["streams"], "=")
            prop_var, prop_streams, prop, prop_dict, prop_rhs = self._contracts(AST["outSpecs"]) if AST["outSpecs"] else ("", "", "", "", [])
            prop_var_adjusted = prop_var if local_vars != "" else "var "+prop_var
            asserts = self._asserts(AST["asserts"])
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
            print node
            return node, prop_dict, extraNodes

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

    def globals(self, AST):
        const = ""
        for k, v in AST.iteritems():
            c = " ".join(y for y in [(k + " " + x + "\n") for x in v])
            const += c
        return const

    def ppInvariant(self, inv):
        new_inv = ""
        for v in inv:
            new_inv += "".join(x for x in (v.split('\n'))[1:])
        return new_inv
            
    def _modularStreams(self, streams, invariants):
        st = ""
        for lhs, rhs in streams.iteritems():
            for node_name, inv in invariants.iteritems():
                if node_name in rhs:
                    new_inv = self.ppInvariant(inv)
                    #st += new_inv + "\n"
                else:
                    st = lhs + " = " + rhs + ";\n"
        return st
    
    def _streams(self, streams):
        st = ""
        for lhs, rhs in streams.iteritems():
            st += lhs + "=" + rhs + ";\n"
        return st

    def _makeNewLocalVars(self, NonMainNode):
        localVars = ""
        for node_id, node in NonMainNode.iteritems():
            localVars += self._local_vars(node["local_vars"])
        return localVars
        
    
    def _invariants(self, inv):
        result = ""
        for node_name, i in inv.iteritems():
            new_inv = self.ppInvariant(i)
            result += new_inv + "\n"
        return result

    def mkMainNode(self, node, invariants, NonMainNode):
        new_local_vars = self._makeNewLocalVars(NonMainNode)
        node_name = node["node_name"]
        input_vars = self._vars_typ(node["input_vars"])
        output_vars = self._vars_typ(node["output_vars"])
        local_vars = self._local_vars(node["local_vars"])
        streams = self._modularStreams(node["streams"], invariants)
        asserts = self._asserts(node["asserts"])
        invariants = self._invariants(invariants)
        props = self._makeProps(node["props"])
        modular_node = (""" node %s (%s) returns (%s) 
            var %s %s
            let
               %s
               %s
               %s
               %s
            tel
        """) % (node_name, input_vars, output_vars, local_vars, new_local_vars, streams, asserts, invariants, props)
        return modular_node