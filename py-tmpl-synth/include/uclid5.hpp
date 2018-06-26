#ifndef __UCLID5_HPP_DEFINED__
#define __UCLID5_HPP_DEFINED__

#include <cassert>

#include <unordered_map>
#include <vector>
#include <memory>

#include "boost/foreach.hpp"
#include "boost/dynamic_bitset.hpp"
#include "boost/logic/tribool.hpp"
#include <z3++.h>
#include <util.hpp>
#include <stack>
#include <smt.hpp>
#include <simplify.hpp>

#include <ast.hpp>

namespace ila
{
    class Abstraction;

    struct LiftingZ3Adapter : public Z3ExprAdapter {
        LiftingZ3Adapter(z3::context& c_) : Z3ExprAdapter(c_, "") 
        {
            simplify = true;
        }

        // List of constants.
        typedef std::map<std::string, z3::expr> expr_map_t;
        typedef std::pair<std::string, z3::expr> map_pair_t;
        expr_map_t constants;
        
        void addConstant(const std::string& name, const Node* init);
        void addConstant(const std::string& name, const z3::expr& val);
        // Convert a boolean variable into a Z3 expression.
        virtual z3::expr getBoolVarExpr(const BoolVar* bv);
        // Convert a bitvector variable into a Z3 expression.
        virtual z3::expr getBitvectorVarExpr(const BitvectorVar* bvv);
        // Convert a mem var into Z3.
        virtual z3::expr getMemVarExpr(const MemVar* mv);
        // convert a variable into an expression.
        z3::expr getVar(const std::string& name, const NodeType& type);

        // dump state of constants for debugging.
        void _dumpConstants();
    };

    class Uclid5Translator
    {
    private:
        // name of the this translator.
        const std::string name;
        // pointer to the abstraction we are translating.
        boost::shared_ptr<Abstraction> abs;  

        // SMT.
        std::shared_ptr<z3::context> c_;
        std::shared_ptr<LiftingZ3Adapter> toZ3;
        std::shared_ptr<z3::solver> S;
        ITESimplifier simplifier;

    public:
        // constructor.
        Uclid5Translator(const std::string& name_, boost::shared_ptr<Abstraction>& a);
        // copy constructor.
        Uclid5Translator(const Uclid5Translator& ut);
        // destructor.
        virtual ~Uclid5Translator();
        // set register to its initial value.
        void initVar(const std::string& reg);
        // set register to a specific value.
        void setVar(const std::string& reg, py::object& value);
        // get expression value. 
        py::list getExprValues(NodeRef& node);
        // set register value.
        void setReg(const std::string& reg, py::long_ value);
        // get next values of register.
        py::list getRegValues(const std::string& reg, int NUM_MAX_VALUES = 64);
        // get the simplified value of this expression.
        NodeRef* simplify(NodeRef& n);
	// translate an ila ast into the corresponding uclid5 program
	std::string getTranslation(NodeRef& node);
    };
}


#endif /* __BOOGIE_HPP_DEFINED__ */

