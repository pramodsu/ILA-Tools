#include <uclid5.hpp>
#include <abstraction.hpp>

namespace ila
{
    void LiftingZ3Adapter::addConstant(const std::string& name, const Node* init)
    {
        z3::expr e = getExpr(init);
        constants.erase(name);
        constants.insert(map_pair_t(name, e));
    }

    void LiftingZ3Adapter::addConstant(const std::string& name, const z3::expr& val)
    {
        constants.erase(name);
        constants.insert(map_pair_t(name, val));
    }

    void LiftingZ3Adapter::_dumpConstants()
    {
        for(auto pos = constants.begin(); pos != constants.end(); pos++) {
            std::cout << pos->first << "-> " << (pos->second) << std::endl;
        }
    }

    z3::expr LiftingZ3Adapter::getBoolVarExpr(const BoolVar* b)
    {
        expr_map_t::iterator pos = constants.find(b->getName());
        if (pos != constants.end()) {
            return pos->second;
        } else {
            return c.bool_const(b->getName().c_str());
        }
    }

    z3::expr LiftingZ3Adapter::getBitvectorVarExpr(const BitvectorVar* bv)
    {
        expr_map_t::iterator pos = constants.find(bv->getName());
        if (pos != constants.end()) {
            return pos->second;
        } else {
            return c.bv_const(bv->getName().c_str(), bv->type.bitWidth);
        }
    }

    z3::expr LiftingZ3Adapter::getMemVarExpr(const MemVar* memv)
    {
        expr_map_t::iterator pos = constants.find(memv->getName());
        if (pos != constants.end()) {
            return pos->second;
        } else {
            auto addrsort = c.bv_sort(memv->type.addrWidth);
            auto datasort = c.bv_sort(memv->type.dataWidth);
            auto memsort = c.array_sort(addrsort, datasort);
            return c.constant(memv->getName().c_str(), memsort);
        }
    }

    z3::expr LiftingZ3Adapter::getVar(const std::string& name, const NodeType& type)
    {
        if (type.isBool()) {
            return c.bool_const(name.c_str());
        } else if (type.isBitvector()) {
            return c.bv_const(name.c_str(), type.bitWidth);
        } else if (type.isMem()) {
            auto addrsort = c.bv_sort(type.addrWidth);
            auto datasort = c.bv_sort(type.dataWidth);
            auto memsort  = c.array_sort(addrsort, datasort);
            return c.constant(name.c_str(), memsort);
        } else {
            ILA_ASSERT(false, "Unexpected type.");
        }
        return c.bool_val(false);
    }

    Uclid5Translator::Uclid5Translator(const std::string& name_, boost::shared_ptr<Abstraction>& a)
      : name(name_)
      , abs(a)
      , c_(new z3::context())
      , toZ3(new LiftingZ3Adapter(*c_))
      , S(new z3::solver(*c_))
      , simplifier(c_, S, toZ3)
    {
    }

    Uclid5Translator::Uclid5Translator(const Uclid5Translator& ut)
      : name(ut.name)
      , abs(ut.abs)
      , c_(ut.c_)
      , toZ3(new LiftingZ3Adapter(*c_))
      , S(new z3::solver(*c_))
      , simplifier(c_, S, toZ3)
    {
    }

    Uclid5Translator::~Uclid5Translator()
    {
    }


    void Uclid5Translator::initVar(const std::string& name)
    {
        const npair_t* vpair = abs->getMapEntry(name);
        // ensure this variable exists.
        if (vpair == NULL) {
            throw new PyILAException(PyExc_RuntimeError, "Undefined register.");
        }
        toZ3->addConstant(name, vpair->init.get());
    }

    void Uclid5Translator::setVar(const std::string& name, py::object& value_)
    {
        const npair_t* vpair = abs->getMapEntry(name);
        // ensure this variable exists.
        if (vpair == NULL) {
            throw new PyILAException(PyExc_RuntimeError, "Undefined register.");
        }
        // check if this is a bitvector.
        if (!vpair->var->type.isBitvector()) {
            throw new PyILAException(
                    PyExc_RuntimeError, 
                    "Expected only a bitvector typed state variable.");
        }
        auto value = to_cpp_int(value_);
        std::unique_ptr<Node> var_value(new BitvectorConst(value, vpair->var->type.bitWidth));
        toZ3->addConstant(name, var_value.get());
    }

    NodeRef* Uclid5Translator::simplify(NodeRef& n)
    {
        //std::cout << *n.node.get() << std::endl;
        //return NULL;
        nptr_t simpl_node = simplifier.simplify((n.node).get());
        return new NodeRef(simpl_node);
        //return 
    }

    py::list Uclid5Translator::getExprValues(NodeRef& node)
    {
        static const int MAX_ITER = 64;
        int iter = 0;

        toZ3->clear();

        nptr_t nptr(node.node);
        z3::expr e = toZ3->getExpr(nptr.get());
        z3::expr c = toZ3->getCnst(nptr.get());
        z3::expr v = toZ3->getVar(nptr->getName(), nptr->type);

        S->push();
        S->add(c);
        S->add(e == v);

        py::list result;

        for (iter = 0; iter < MAX_ITER && S->check() == z3::sat; iter++) {
            z3::model m = S->get_model();
            z3::expr v_expr = m.eval(v);
            if (nptr->type.isBool()) {
                bool value;
                Z3_lbool vz = v_expr.bool_value();
                if (vz == Z3_L_FALSE) {
                    value = false;
                } else if (vz == Z3_L_TRUE) {
                    value = true;
                } else {
                    throw PyILAException(PyExc_RuntimeError, "Undefined boolean value.");
                }
                result.append(value);
            } else if(nptr->type.isBitvector()) {
                using namespace py;
                std::string v_str = v_expr.get_decimal_string(0);
                PyObject* l_e = PyInt_FromString((char*) v_str.c_str(), NULL, 0);
                object o_e(handle<>(borrowed(l_e)));
                result.append(o_e);
            } else {
                throw PyILAException(PyExc_RuntimeError, "Unsupported type.");
            }
            S->add(v != v_expr);
        }
        S->pop();
        return result;
    }

    std::string Uclid5Translator::getTranslation(NodeRef& node)
    {
	//Completely ripped off from smt.cpp
	std::string program;
	program.clear();
	nptr_t nptr(node.node);
	auto n = nptr.get();

	// handle the various types.
        const BoolVar* boolvar = NULL; 
        const BoolConst* boolconst = NULL;
        const BoolOp* boolop = NULL;
        const BoolChoice* bchoiceop = NULL;

        const BitvectorVar* bvvar = NULL;
        const BitvectorConst* bvconst = NULL;
        const BitvectorOp* bvop = NULL;
        const BitvectorChoice* bvchoiceop = NULL;
        const BVInRange* inrangeop = NULL;

        const MemVar* memvar = NULL;
        const MemConst* memconst = NULL;
        const MemOp*  memop = NULL;
        const MemChoice* mchoiceop = NULL;

        const FuncVar* funcvar = NULL;

        //log2("Z3ExprAdapter._populateExprMap") << "entering: " << *n << std::endl;

        //// booleans ////
        if ((boolvar = dynamic_cast<const BoolVar*>(n))) {
		program = nptr->getName();
//            	z3::expr r = getBoolVarExpr(boolvar);
//            	if (simplify) r = r.simplify();
//            	log2("Z3ExprAdapter._populateExprMap") << *n << " --> " << r << std::endl;
//            	exprmap.insert({n, r});
        } else if ((boolconst = dynamic_cast<const BoolConst*>(n))) {
		if (boolconst->val()) 
			program = "true";
		else
			program = "false";
//            	z3::expr r = c.bool_val(boolconst->val());
//            	if (simplify) r = r.simplify();
//            	log2("Z3ExprAdapter._populateExprMap") << *n << " --> " << r << std::endl;
//            	exprmap.insert({n, r});
        } else if ((boolop = dynamic_cast<const BoolOp*>(n))) {
		switch(boolop->getOp()) {
			case BoolOp::INVALID	: { program = "INVALID"; break; }
			case BoolOp::NOT	: { NodeRef a1(boolop->arg(0)); program = "!(" + getTranslation(a1) + ")"; break; }
			case BoolOp::AND 	: { NodeRef a1(boolop->arg(0)); NodeRef a2(boolop->arg(1)); 
						  program = "(" + getTranslation(a1) + " && " + getTranslation(a2) + ")"; break;}
			case BoolOp::OR 	: { NodeRef a1(boolop->arg(0)); NodeRef a2(boolop->arg(1)); 
						  program = "(" + getTranslation(a1) + " || " + getTranslation(a2) + ")"; break;}
			case BoolOp::XOR 	: { NodeRef a1(boolop->arg(0)); NodeRef a2(boolop->arg(1)); 
						  program = "(" + getTranslation(a1) + " ^ " + getTranslation(a2) + ")"; break;}
			case BoolOp::XNOR 	: { NodeRef a1(boolop->arg(0)); NodeRef a2(boolop->arg(1)); 
						  program = "!(" + getTranslation(a1) + " ^ " + getTranslation(a2) + ")"; break; }
			case BoolOp::NAND 	: { NodeRef a1(boolop->arg(0)); NodeRef a2(boolop->arg(1)); 
						  program = "!(" + getTranslation(a1) + " && " + getTranslation(a2) + ")"; break; }
			case BoolOp::NOR 	: { NodeRef a1(boolop->arg(0)); NodeRef a2(boolop->arg(1)); 
						  program = "!(" + getTranslation(a1) + " || " + getTranslation(a2) + ")"; break; }
	 		case BoolOp::IMPLY 	: { NodeRef a1(boolop->arg(0)); NodeRef a2(boolop->arg(1)); 
						  program = "(" + getTranslation(a1) + " ==> " + getTranslation(a2) + ")" ; break; }
			case BoolOp::ULT 	:
			case BoolOp::SLT 	: { NodeRef a1(boolop->arg(0)); NodeRef a2(boolop->arg(1)); 
						  program = "(" + getTranslation(a1) + " < " + getTranslation(a2) + ")"; break; }
			case BoolOp::UGT 	:
			case BoolOp::SGT 	: { NodeRef a1(boolop->arg(0)); NodeRef a2(boolop->arg(1)); 
						  program = "(" + getTranslation(a1) + " > " + getTranslation(a2) + ")" ; break; }

			case BoolOp::ULE 	:
			case BoolOp::SLE 	: { NodeRef a1(boolop->arg(0)); NodeRef a2(boolop->arg(1)); 
						  program = "(" + getTranslation(a1) + " <= " + getTranslation(a2) + ")"; break; }
			case BoolOp::UGE 	:
			case BoolOp::SGE 	: { NodeRef a1(boolop->arg(0)); NodeRef a2(boolop->arg(1)); 
						  program = "(" + getTranslation(a1) + " >= " + getTranslation(a2) + ")"; break; }
			case BoolOp::EQUAL 	: { NodeRef a1(boolop->arg(0)); NodeRef a2(boolop->arg(1)); 
						  program = "(" + getTranslation(a1) + " == " + getTranslation(a2) + ")"; break; }
 			case BoolOp::IF 	: { NodeRef a1(boolop->arg(0)); NodeRef a2(boolop->arg(1)); NodeRef a3(boolop->arg(2));
						  program = "if (" + getTranslation(a1) + ")" + " then { " + getTranslation(a2) + " }" 							 +  " else { " + getTranslation(a3) + " }"; break;}
			case BoolOp::DISTINCT 	: { NodeRef a1(boolop->arg(0)); NodeRef a2(boolop->arg(1));
						  program = "(" + getTranslation(a1) + " != " + getTranslation(a2) + ")"; break; }
			default:	{ program = "Unsupported"; }
		}



//    		z3::expr r = getBoolOpExpr(boolop);
//    	        if (simplify) r = r.simplify();
//        	log2("Z3ExprAdapter._populateExprMap") << *n << " --> " << r << std::endl;
//            	exprmap.insert({n, r});
        } else if((bchoiceop = dynamic_cast<const BoolChoice*>(n))) {
	 	program = "BChoiceUnsupported";
//              z3::expr r = getChoiceExpr(bchoiceop);
//             if (simplify) r = r.simplify();
//            log2("Z3ExprAdapter._populateExprMap") << *n << " --> " << r << std::endl;
//            exprmap.insert({n, r});

        //// bitvectors ////
        } else if((bvvar = dynamic_cast<const BitvectorVar*>(n))) {
	      	program = nptr->getName();
//            z3::expr r = getBitvectorVarExpr(bvvar);
//            if (simplify) r = r.simplify();
//            log2("Z3ExprAdapter._populateExprMap") << *n << " --> " << r << std::endl;
//            exprmap.insert({n, r});
        } else if((bvconst = dynamic_cast<const BitvectorConst*>(n))) {
		program = bvconst->vstr() + "bv" + std::to_string(nptr->type.bitWidth);
//            	z3::expr r = c.bv_val(bvconst->vstr().c_str(), bvconst->type.bitWidth);
//            	if (simplify) r = r.simplify();
//            	log2("Z3ExprAdapter._populateExprMap") << *n << " --> " << r << std::endl;
//            	exprmap.insert({n, r});
        } else if ((bvop = dynamic_cast<const BitvectorOp*>(n))) {
		switch(bvop->getOp()) {
			case BitvectorOp::INVALID 	: { program = "InvalidBVOP"; break; }
			case BitvectorOp::NEGATE	: { NodeRef a1(bvop->arg(0)); program = "~(" + getTranslation(a1) + ")"; break; }
			case BitvectorOp::COMPLEMENT	: { NodeRef a1(bvop->arg(0)); program = "~(" + getTranslation(a1) + ")"; break; }
			case BitvectorOp::LROTATE	: { NodeRef a1(bvop->arg(0)); program = "lrot(" + getTranslation(a1) + ")"; break; }
			case BitvectorOp::RROTATE	: { NodeRef a1(bvop->arg(0)); program = "rrot(" + getTranslation(a1) + ")"; break; }
			case BitvectorOp::Z_EXT	: { NodeRef a1(bvop->arg(0)); program = "zeroext(" + getTranslation(a1) + ")"; break; }
			case BitvectorOp::S_EXT	: { NodeRef a1(bvop->arg(0)); program = "signext(" + getTranslation(a1) + ")"; break; }
			case BitvectorOp::EXTRACT	: { NodeRef a1(bvop->arg(0)); program = "extract(" + getTranslation(a1) + ")"; break; }
			case BitvectorOp::ADD 	: { NodeRef a1(bvop->arg(0)); NodeRef a2(bvop->arg(1)); 
						  program = "(" + getTranslation(a1) + " + " + getTranslation(a2) + ")"; break;}
			case BitvectorOp::SUB 	: { NodeRef a1(bvop->arg(0)); NodeRef a2(bvop->arg(1)); 
						  program = "(" + getTranslation(a1) + " - " + getTranslation(a2) + ")"; break;}
			case BitvectorOp::AND 	: { NodeRef a1(bvop->arg(0)); NodeRef a2(bvop->arg(1)); 
						  program = "(" + getTranslation(a1) + " & " + getTranslation(a2) + ")"; break;}
			case BitvectorOp::OR 	: { NodeRef a1(bvop->arg(0)); NodeRef a2(bvop->arg(1)); 
						  program = "(" + getTranslation(a1) + " | " + getTranslation(a2) + ")"; break;}
			case BitvectorOp::XOR 	: { NodeRef a1(bvop->arg(0)); NodeRef a2(bvop->arg(1)); 
						  program = "(" + getTranslation(a1) + " ^ " + getTranslation(a2) + ")"; break;}
			case BitvectorOp::XNOR 	: { NodeRef a1(bvop->arg(0)); NodeRef a2(bvop->arg(1)); 
						  program = "~(" + getTranslation(a1) + " ^ " + getTranslation(a2) + ")";  break;}
			case BitvectorOp::NAND 	: { NodeRef a1(bvop->arg(0)); NodeRef a2(bvop->arg(1)); 
						  program = "~(" + getTranslation(a1) + " & " + getTranslation(a2) + ")"; break;}
			case BitvectorOp::NOR 	: { NodeRef a1(bvop->arg(0)); NodeRef a2(bvop->arg(1)); 
						  program = "~(" + getTranslation(a1) + " | " + getTranslation(a2) + ")"; break;}
			case BitvectorOp::SDIV 	: 
			case BitvectorOp::UDIV 	: { program = "DIVNotSupported" ; break;}
			
			case BitvectorOp::SREM 	:
			case BitvectorOp::UREM	: { program = "RemNotSupported" ; break;}
			case BitvectorOp::SMOD 	: { program = "SmodNotSupported" ; break;}
			case BitvectorOp::SHL 	: { NodeRef a1(bvop->arg(0)); NodeRef a2(bvop->arg(1));
						  program = "shl(" + getTranslation(a1) + "," + getTranslation(a2) + ")"; break;}
			case BitvectorOp::LSHR 	: { NodeRef a1(bvop->arg(0)); NodeRef a2(bvop->arg(1));
						  program = "lshr(" + getTranslation(a1) + "," + getTranslation(a2) + ")"; break;}
			case BitvectorOp::ASHR 	: { NodeRef a1(bvop->arg(0)); NodeRef a2(bvop->arg(1));
						  program = "ashr(" + getTranslation(a1) + "," + getTranslation(a2) + ")"; break;}
			case BitvectorOp::MUL 	: { NodeRef a1(bvop->arg(0)); NodeRef a2(bvop->arg(1)); 
						  program = getTranslation(a1) + " * " + getTranslation(a2); break;}
			case BitvectorOp::CONCAT 	: { NodeRef a1(bvop->arg(0)); NodeRef a2(bvop->arg(1)); 
						  program = "(" + getTranslation(a1) + " ++ " + getTranslation(a2) + ")"; break;}
			case BitvectorOp::GET_BIT    : { program = "GETBitUnsupported"; break; }
			case BitvectorOp::READMEM 	: { NodeRef a1(bvop->arg(0)); NodeRef a2(bvop->arg(1)); 
						  program = getTranslation(a1) + "[" + getTranslation(a2) + "]"; break;}
			case BitvectorOp::READMEMBLOCK : { program = "READMEMBLOCKUnsupported"; break; }
	 		case BitvectorOp::IF 	: { NodeRef a1(bvop->arg(0)); NodeRef a2(bvop->arg(1)); NodeRef a3(bvop->arg(2));
						  program = "if (" + getTranslation(a1) + ")" + " then { " + getTranslation(a2) + " }" +
						  " else { " + getTranslation(a3) + " }"; break;}
			case BitvectorOp::APPLY_FUNC :
			default: 	{ program = "Unsupported"; }
		}	  
//            	z3::expr r = getBvOpExpr(bvop);
//            	if (simplify) r = r.simplify();
//            	log2("Z3ExprAdapter._populateExprMap") << *n << " --> " << r << std::endl;
//            	exprmap.insert({n, r});
        } else if ((bvchoiceop = dynamic_cast<const BitvectorChoice*>(n))) {
		program = "BvChoiceUnsuported";
//            	z3::expr r = getChoiceExpr(bvchoiceop);
//            	if (simplify) r = r.simplify();
//            	log2("Z3ExprAdapter._populateExprMap") << *n << " --> " << r << std::endl;
//            	exprmap.insert({n, r});
        } else if ((inrangeop = dynamic_cast<const BVInRange*>(n))) {
		program = "BVInrangeUnsupported";
//            	z3::expr r = getBVInRangeExpr(inrangeop);
//            	if (simplify) r = r.simplify();
//           	log2("Z3ExprAdapter._populateExprMap") << *n << " --> " << r << std::endl;
//            	exprmap.insert({n, r});

        //// memories ////
        } else if ((memvar = dynamic_cast<const MemVar*>(n))) {
	      	program = nptr->getName();
//            	z3::expr r = getMemVarExpr(memvar);
//            	if (simplify) r = r.simplify();
//            	log2("Z3ExprAdapter._populateExprMap") << *n << " --> " << r << std::endl;
//            	exprmap.insert({n, r});
        } else if ((memconst = dynamic_cast<const MemConst*>(n))) {
		program = "MemConstNotSupported";
//            	z3::expr r = memconst->memvalues.toZ3(c);
//            	if (simplify) r = r.simplify();
//            	log2("Z3ExprAdapter._populateExprMap") << *n << " --> " << r << std::endl;
//            	exprmap.insert({n, r});
        } else if ((memop = dynamic_cast<const MemOp*>(n))) {
	     	switch(memop->getOp()) {
			case MemOp::INVALID 	: { program = "InvalidMemOp"; break; }
			case MemOp::STORE	: { NodeRef a1(memop->arg(0)); NodeRef a2(memop->arg(1)); NodeRef a3(memop->arg(2));
						program = getTranslation(a1) + "[" + getTranslation(a2) + "->" + getTranslation(a3) + "]"; }
			case MemOp::ITE 	: { NodeRef a1(memop->arg(0)); NodeRef a2(memop->arg(1)); NodeRef a3(memop->arg(2));
						  program = "if (" + getTranslation(a1) + ")" + " then { " + getTranslation(a2) + " }" +
						  " else { " + getTranslation(a3) + " }"; break;}
			case MemOp::STOREBLOCK :
			default:	{ program = "InvalidMemOP"; }
		}


/*          	z3::expr r = getMemOpExpr(memop);
            	if (simplify) r = r.simplify();
            	log2("Z3ExprAdapter._populateExprMap") << *n << " --> " << r << std::endl;
            	exprmap.insert({n, r}); */
        } else if ((mchoiceop = dynamic_cast<const MemChoice*>(n))) {
	    	program = "MemChoiceNotSupported";
/*
            	z3::expr r = getChoiceExpr(mchoiceop);
            	if (simplify) r = r.simplify();
            	log2("Z3ExprAdapter._populateExprMap") << *n << " --> " << r << std::endl;
            	exprmap.insert({n, r});
	*/
        //// Functions ////
        } else if ((funcvar = dynamic_cast<const FuncVar*>(n))) {
	      	program = "FuncVarsNotSupported";
/*            	z3::expr r = getFuncVarExpr(funcvar);
            	//if (simplify) r = r.simplify();
            	log2("Z3ExprAdapter._populateExprMap") << *n << " --> " << r << std::endl;
            	exprmap.insert({n, r}); */
        }
	
	return program;
    }	
}
