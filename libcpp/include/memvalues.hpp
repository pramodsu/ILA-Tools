#ifndef __MEMVALUES_HPP_DEFINED__
#define __MEMVALUES_HPP_DEFINED__

#include <iostream>
#include <map>

#include <common.hpp>
#include <ast/node.hpp>
#include <type.hpp>

#include <boost/python.hpp>
#include <z3++.h>

namespace ila
{
    class Z3ExprAdapter;
    class MemVar;

    // This structure represents a memory with known values.
    // It is passed into python during synthesis.
    struct MemValues
    {
        typedef std::map<mp_int_t, mp_int_t> map_t;

        NodeType type;
        const mp_int_t MAX_ADDR;

        mp_int_t def_value;
        map_t values;

        // constructor.
        MemValues(int addrWidth, int dataWidth, const py::object& def_val);
        // construct from a model.
        MemValues(Z3ExprAdapter& c, const z3::model& m, const MemVar* mem);
        // destructor.
        ~MemValues();

        // return def_value
        py::object getDefault() const;
        // set def_value.
        void setDefault(const py::object& dv);
        // get nondefault values.
        py::object getValues() const;
        // __getitem__
        py::object getItem (const py::object& index) const;
        // __setitem__
        void setItem (const py::object& index, const py::object& value);

        // equality for python.
        bool eq(const MemValues& mv) const { return *this == mv; }
        // equality.
        bool operator==(const MemValues& mv) const;
        // convert to z3.
        z3::expr toZ3(z3::context& c) const;
    };
    std::ostream& operator<<(std::ostream& out, const MemValues& mv);
}

#endif
