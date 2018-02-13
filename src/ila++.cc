/// \file
/// Source for the c++ API.

#include "ila++.h"
#include "ila/instr_lvl_abs.h"

namespace ila {

/******************************************************************************/
// ExprRef
/******************************************************************************/
ExprRef::ExprRef(std::shared_ptr<Expr> ptr) : ptr_(ptr) {}

ExprRef::~ExprRef() {}

ExprRef ExprRef::operator-() const {
  auto v = ExprFuse::Negate(get());
  return ExprRef(v);
}

ExprRef ExprRef::operator+(const ExprRef& rhs) const {
  auto v = ExprFuse::Add(get(), rhs.get());
  return ExprRef(v);
}

ExprRef BoolConst(bool val) {
  auto v = ExprFuse::BoolConst(val);
  return ExprRef(v);
}

ExprRef BvConst(const int& bv_val, const int& bit_width) {
  auto v = ExprFuse::BvConst(bv_val, bit_width);
  return ExprRef(v);
}

ExprRef MemConst(const int& def_val, const std::map<int, int>& vals,
                 const int& addr_width, const int& data_width) {
  auto v = ExprFuse::MemConst(MemVal(def_val, vals), addr_width, data_width);
  return ExprRef(v);
}

/******************************************************************************/
// InstrRef
/******************************************************************************/
InstrRef::InstrRef(std::shared_ptr<Instr> ptr) : ptr_(ptr) {}

InstrRef::~InstrRef() {}

void InstrRef::SetDecode(const ExprRef& decode) {
  ptr_->SetDecode(decode.get());
}

void InstrRef::SetUpdate(const ExprRef& state, const ExprRef& update) {
  ptr_->AddUpdate(state.get(), update.get());
}

} // namespace ila
