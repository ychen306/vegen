
#include "InstSema.h"
#include "MatchingUtil.h"

using namespace llvm;
using namespace PatternMatch;
    

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1;
    bool Matched = hasBitWidth(V, 16) &&
PatternMatch::match(V, m_c_Add(
      m_SExt(
        m_Value(tmp0)),
      m_SExt(
        m_Value(tmp1)))) &&
hasBitWidth(tmp0, 8) &&
hasBitWidth(tmp1, 8);
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation0;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1;
    bool Matched = hasBitWidth(V, 32) &&
PatternMatch::match(V, m_c_Add(
      m_SExt(
        m_Value(tmp0)),
      m_SExt(
        m_Value(tmp1)))) &&
hasBitWidth(tmp0, 16) &&
hasBitWidth(tmp1, 16);
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation1;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1;
    bool Matched = hasBitWidth(V, 64) &&
PatternMatch::match(V, m_c_Add(
      m_SExt(
        m_Value(tmp0)),
      m_SExt(
        m_Value(tmp1)))) &&
hasBitWidth(tmp0, 32) &&
hasBitWidth(tmp1, 32);
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation2;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1;
    bool Matched = hasBitWidth(V, 16) &&
PatternMatch::match(V, m_c_Add(
      m_ZExt(
        m_Value(tmp0)),
      m_ZExt(
        m_Value(tmp1)))) &&
hasBitWidth(tmp0, 8) &&
hasBitWidth(tmp1, 8);
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation3;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1;
    bool Matched = hasBitWidth(V, 32) &&
PatternMatch::match(V, m_c_Add(
      m_ZExt(
        m_Value(tmp0)),
      m_ZExt(
        m_Value(tmp1)))) &&
hasBitWidth(tmp0, 16) &&
hasBitWidth(tmp1, 16);
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation4;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1;
    bool Matched = hasBitWidth(V, 64) &&
PatternMatch::match(V, m_c_Add(
      m_ZExt(
        m_Value(tmp0)),
      m_ZExt(
        m_Value(tmp1)))) &&
hasBitWidth(tmp0, 32) &&
hasBitWidth(tmp1, 32);
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation5;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1;
    bool Matched = hasBitWidth(V, 16) &&
PatternMatch::match(V, m_c_Add(
      m_SExt(
        m_Value(tmp0)),
      m_Value(tmp1))) &&
hasBitWidth(tmp0, 8) &&
hasBitWidth(tmp1, 16);
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation6;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1;
    bool Matched = hasBitWidth(V, 32) &&
PatternMatch::match(V, m_c_Add(
      m_SExt(
        m_Value(tmp0)),
      m_Value(tmp1))) &&
hasBitWidth(tmp0, 16) &&
hasBitWidth(tmp1, 32);
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation7;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1;
    bool Matched = hasBitWidth(V, 64) &&
PatternMatch::match(V, m_c_Add(
      m_SExt(
        m_Value(tmp0)),
      m_Value(tmp1))) &&
hasBitWidth(tmp0, 32) &&
hasBitWidth(tmp1, 64);
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation8;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1;
    bool Matched = hasBitWidth(V, 16) &&
PatternMatch::match(V, m_c_Add(
      m_ZExt(
        m_Value(tmp0)),
      m_Value(tmp1))) &&
hasBitWidth(tmp0, 8) &&
hasBitWidth(tmp1, 16);
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation9;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1;
    bool Matched = hasBitWidth(V, 32) &&
PatternMatch::match(V, m_c_Add(
      m_ZExt(
        m_Value(tmp0)),
      m_Value(tmp1))) &&
hasBitWidth(tmp0, 16) &&
hasBitWidth(tmp1, 32);
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation10;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1;
    bool Matched = hasBitWidth(V, 64) &&
PatternMatch::match(V, m_c_Add(
      m_ZExt(
        m_Value(tmp0)),
      m_Value(tmp1))) &&
hasBitWidth(tmp0, 32) &&
hasBitWidth(tmp1, 64);
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation11;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1;
    bool Matched = hasBitWidth(V, 8) &&
PatternMatch::match(V, m_Trunc(
      m_LShr(
        m_c_Add(
          m_SExt(
            m_Value(tmp0)),
          m_SExt(
            m_Value(tmp1))),
        m_SpecificInt(APInt(16, "1", 10))))) &&
hasBitWidth(tmp0, 8) &&
hasBitWidth(tmp1, 8);
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation12;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1;
    bool Matched = hasBitWidth(V, 16) &&
PatternMatch::match(V, m_Trunc(
      m_LShr(
        m_c_Add(
          m_SExt(
            m_Value(tmp0)),
          m_SExt(
            m_Value(tmp1))),
        m_SpecificInt(APInt(32, "1", 10))))) &&
hasBitWidth(tmp0, 16) &&
hasBitWidth(tmp1, 16);
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation13;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1;
    bool Matched = hasBitWidth(V, 32) &&
PatternMatch::match(V, m_Trunc(
      m_LShr(
        m_c_Add(
          m_SExt(
            m_Value(tmp0)),
          m_SExt(
            m_Value(tmp1))),
        m_SpecificInt(APInt(64, "1", 10))))) &&
hasBitWidth(tmp0, 32) &&
hasBitWidth(tmp1, 32);
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation14;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1;
    bool Matched = hasBitWidth(V, 8) &&
PatternMatch::match(V, m_Trunc(
      m_LShr(
        m_c_Add(
          m_ZExt(
            m_Value(tmp0)),
          m_ZExt(
            m_Value(tmp1))),
        m_SpecificInt(APInt(16, "1", 10))))) &&
hasBitWidth(tmp0, 8) &&
hasBitWidth(tmp1, 8);
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation15;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1;
    bool Matched = hasBitWidth(V, 16) &&
PatternMatch::match(V, m_Trunc(
      m_LShr(
        m_c_Add(
          m_ZExt(
            m_Value(tmp0)),
          m_ZExt(
            m_Value(tmp1))),
        m_SpecificInt(APInt(32, "1", 10))))) &&
hasBitWidth(tmp0, 16) &&
hasBitWidth(tmp1, 16);
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation16;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1;
    bool Matched = hasBitWidth(V, 32) &&
PatternMatch::match(V, m_Trunc(
      m_LShr(
        m_c_Add(
          m_ZExt(
            m_Value(tmp0)),
          m_ZExt(
            m_Value(tmp1))),
        m_SpecificInt(APInt(64, "1", 10))))) &&
hasBitWidth(tmp0, 32) &&
hasBitWidth(tmp1, 32);
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation17;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1;
    bool Matched = hasBitWidth(V, 8) &&
PatternMatch::match(V, m_Trunc(
      m_LShr(
        m_c_Add(
          m_c_Add(
            m_SExt(
              m_Value(tmp0)),
            m_SpecificInt(APInt(16, "1", 10))),
          m_SExt(
            m_Value(tmp1))),
        m_SpecificInt(APInt(16, "1", 10))))) &&
hasBitWidth(tmp0, 8) &&
hasBitWidth(tmp1, 8);
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation18;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1;
    bool Matched = hasBitWidth(V, 16) &&
PatternMatch::match(V, m_Trunc(
      m_LShr(
        m_c_Add(
          m_c_Add(
            m_SExt(
              m_Value(tmp0)),
            m_SpecificInt(APInt(32, "1", 10))),
          m_SExt(
            m_Value(tmp1))),
        m_SpecificInt(APInt(32, "1", 10))))) &&
hasBitWidth(tmp0, 16) &&
hasBitWidth(tmp1, 16);
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation19;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1;
    bool Matched = hasBitWidth(V, 32) &&
PatternMatch::match(V, m_Trunc(
      m_LShr(
        m_c_Add(
          m_c_Add(
            m_SExt(
              m_Value(tmp0)),
            m_SpecificInt(APInt(64, "1", 10))),
          m_SExt(
            m_Value(tmp1))),
        m_SpecificInt(APInt(64, "1", 10))))) &&
hasBitWidth(tmp0, 32) &&
hasBitWidth(tmp1, 32);
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation20;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1;
    bool Matched = hasBitWidth(V, 8) &&
PatternMatch::match(V, m_Trunc(
      m_LShr(
        m_c_Add(
          m_c_Add(
            m_ZExt(
              m_Value(tmp0)),
            m_SpecificInt(APInt(16, "1", 10))),
          m_ZExt(
            m_Value(tmp1))),
        m_SpecificInt(APInt(16, "1", 10))))) &&
hasBitWidth(tmp0, 8) &&
hasBitWidth(tmp1, 8);
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation21;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1;
    bool Matched = hasBitWidth(V, 16) &&
PatternMatch::match(V, m_Trunc(
      m_LShr(
        m_c_Add(
          m_c_Add(
            m_ZExt(
              m_Value(tmp0)),
            m_SpecificInt(APInt(32, "1", 10))),
          m_ZExt(
            m_Value(tmp1))),
        m_SpecificInt(APInt(32, "1", 10))))) &&
hasBitWidth(tmp0, 16) &&
hasBitWidth(tmp1, 16);
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation22;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1;
    bool Matched = hasBitWidth(V, 32) &&
PatternMatch::match(V, m_Trunc(
      m_LShr(
        m_c_Add(
          m_c_Add(
            m_ZExt(
              m_Value(tmp0)),
            m_SpecificInt(APInt(64, "1", 10))),
          m_ZExt(
            m_Value(tmp1))),
        m_SpecificInt(APInt(64, "1", 10))))) &&
hasBitWidth(tmp0, 32) &&
hasBitWidth(tmp1, 32);
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation23;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1; Value *tmp2; Value *tmp3; Value *tmp4; Value *tmp5;
    bool Matched = hasBitWidth(V, 8) &&
PatternMatch::match(V, m_Trunc(
      m_SelectOnCmp(CmpInst::Predicate::ICMP_SGT,
        m_c_Add(
          m_SExt(
            m_Value(tmp0)),
          m_SExt(
            m_Value(tmp1))),
        m_SpecificInt(APInt(16, "127", 10)),
        m_SpecificInt(APInt(16, "127", 10)),
        m_SelectOnCmp(CmpInst::Predicate::ICMP_SLT,
          m_c_Add(
            m_SExt(
              m_Value(tmp2)),
            m_SExt(
              m_Value(tmp3))),
          m_SpecificInt(APInt(16, "65409", 10)),
          m_SpecificInt(APInt(16, "65408", 10)),
          m_c_Add(
            m_SExt(
              m_Value(tmp4)),
            m_SExt(
              m_Value(tmp5))))))) &&
hasBitWidth(tmp0, 8) &&
tmp0 == tmp2 &&
tmp0 == tmp4 &&
hasBitWidth(tmp1, 8) &&
tmp1 == tmp3 &&
tmp1 == tmp5;
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation24;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1; Value *tmp2; Value *tmp3; Value *tmp4; Value *tmp5;
    bool Matched = hasBitWidth(V, 16) &&
PatternMatch::match(V, m_Trunc(
      m_SelectOnCmp(CmpInst::Predicate::ICMP_SGT,
        m_c_Add(
          m_SExt(
            m_Value(tmp0)),
          m_SExt(
            m_Value(tmp1))),
        m_SpecificInt(APInt(32, "32767", 10)),
        m_SpecificInt(APInt(32, "32767", 10)),
        m_SelectOnCmp(CmpInst::Predicate::ICMP_SLT,
          m_c_Add(
            m_SExt(
              m_Value(tmp2)),
            m_SExt(
              m_Value(tmp3))),
          m_SpecificInt(APInt(32, "4294934529", 10)),
          m_SpecificInt(APInt(32, "4294934528", 10)),
          m_c_Add(
            m_SExt(
              m_Value(tmp4)),
            m_SExt(
              m_Value(tmp5))))))) &&
hasBitWidth(tmp0, 16) &&
tmp0 == tmp2 &&
tmp0 == tmp4 &&
hasBitWidth(tmp1, 16) &&
tmp1 == tmp3 &&
tmp1 == tmp5;
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation25;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1; Value *tmp2; Value *tmp3; Value *tmp4; Value *tmp5;
    bool Matched = hasBitWidth(V, 32) &&
PatternMatch::match(V, m_Trunc(
      m_SelectOnCmp(CmpInst::Predicate::ICMP_SGT,
        m_c_Add(
          m_SExt(
            m_Value(tmp0)),
          m_SExt(
            m_Value(tmp1))),
        m_SpecificInt(APInt(64, "2147483647", 10)),
        m_SpecificInt(APInt(64, "2147483647", 10)),
        m_SelectOnCmp(CmpInst::Predicate::ICMP_SLT,
          m_c_Add(
            m_SExt(
              m_Value(tmp2)),
            m_SExt(
              m_Value(tmp3))),
          m_SpecificInt(APInt(64, "18446744071562067969", 10)),
          m_SpecificInt(APInt(64, "18446744071562067968", 10)),
          m_c_Add(
            m_SExt(
              m_Value(tmp4)),
            m_SExt(
              m_Value(tmp5))))))) &&
hasBitWidth(tmp0, 32) &&
tmp0 == tmp2 &&
tmp0 == tmp4 &&
hasBitWidth(tmp1, 32) &&
tmp1 == tmp3 &&
tmp1 == tmp5;
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation26;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1; Value *tmp2; Value *tmp3;
    bool Matched = hasBitWidth(V, 8) &&
PatternMatch::match(V, m_Trunc(
      m_SelectOnCmp(CmpInst::Predicate::ICMP_ULT,
        m_c_Add(
          m_ZExt(
            m_Value(tmp0)),
          m_ZExt(
            m_Value(tmp1))),
        m_SpecificInt(APInt(16, "255", 10)),
        m_c_Add(
          m_ZExt(
            m_Value(tmp2)),
          m_ZExt(
            m_Value(tmp3))),
        m_SpecificInt(APInt(16, "255", 10))))) &&
hasBitWidth(tmp0, 8) &&
tmp0 == tmp2 &&
hasBitWidth(tmp1, 8) &&
tmp1 == tmp3;
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation27;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1; Value *tmp2; Value *tmp3;
    bool Matched = hasBitWidth(V, 16) &&
PatternMatch::match(V, m_Trunc(
      m_SelectOnCmp(CmpInst::Predicate::ICMP_ULT,
        m_c_Add(
          m_ZExt(
            m_Value(tmp0)),
          m_ZExt(
            m_Value(tmp1))),
        m_SpecificInt(APInt(32, "65535", 10)),
        m_c_Add(
          m_ZExt(
            m_Value(tmp2)),
          m_ZExt(
            m_Value(tmp3))),
        m_SpecificInt(APInt(32, "65535", 10))))) &&
hasBitWidth(tmp0, 16) &&
tmp0 == tmp2 &&
hasBitWidth(tmp1, 16) &&
tmp1 == tmp3;
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation28;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1; Value *tmp2; Value *tmp3;
    bool Matched = hasBitWidth(V, 32) &&
PatternMatch::match(V, m_Trunc(
      m_SelectOnCmp(CmpInst::Predicate::ICMP_ULT,
        m_c_Add(
          m_ZExt(
            m_Value(tmp0)),
          m_ZExt(
            m_Value(tmp1))),
        m_SpecificInt(APInt(64, "4294967295", 10)),
        m_c_Add(
          m_ZExt(
            m_Value(tmp2)),
          m_ZExt(
            m_Value(tmp3))),
        m_SpecificInt(APInt(64, "4294967295", 10))))) &&
hasBitWidth(tmp0, 32) &&
tmp0 == tmp2 &&
hasBitWidth(tmp1, 32) &&
tmp1 == tmp3;
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation29;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1;
    bool Matched = hasBitWidth(V, 8) &&
PatternMatch::match(V, m_Trunc(
      m_LShr(
        m_c_Add(
          m_ZExt(
            m_Value(tmp0)),
          m_ZExt(
            m_Value(tmp1))),
        m_SpecificInt(APInt(32, "8", 10))))) &&
hasBitWidth(tmp0, 16) &&
hasBitWidth(tmp1, 16);
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation30;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1;
    bool Matched = hasBitWidth(V, 16) &&
PatternMatch::match(V, m_Trunc(
      m_LShr(
        m_c_Add(
          m_ZExt(
            m_Value(tmp0)),
          m_ZExt(
            m_Value(tmp1))),
        m_SpecificInt(APInt(64, "16", 10))))) &&
hasBitWidth(tmp0, 32) &&
hasBitWidth(tmp1, 32);
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation31;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1;
    bool Matched = hasBitWidth(V, 8) &&
PatternMatch::match(V, m_Trunc(
      m_LShr(
        m_c_Add(
          m_c_Add(
            m_ZExt(
              m_Value(tmp0)),
            m_SpecificInt(APInt(32, "128", 10))),
          m_ZExt(
            m_Value(tmp1))),
        m_SpecificInt(APInt(32, "8", 10))))) &&
hasBitWidth(tmp0, 16) &&
hasBitWidth(tmp1, 16);
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation32;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1;
    bool Matched = hasBitWidth(V, 16) &&
PatternMatch::match(V, m_Trunc(
      m_LShr(
        m_c_Add(
          m_c_Add(
            m_ZExt(
              m_Value(tmp0)),
            m_SpecificInt(APInt(64, "32768", 10))),
          m_ZExt(
            m_Value(tmp1))),
        m_SpecificInt(APInt(64, "16", 10))))) &&
hasBitWidth(tmp0, 32) &&
hasBitWidth(tmp1, 32);
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation33;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1;
    bool Matched = hasBitWidth(V, 8) &&
PatternMatch::match(V, m_c_Mul(
      m_Value(tmp0),
      m_Value(tmp1))) &&
hasBitWidth(tmp0, 8) &&
hasBitWidth(tmp1, 8);
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation34;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1;
    bool Matched = hasBitWidth(V, 16) &&
PatternMatch::match(V, m_c_Mul(
      m_Value(tmp0),
      m_Value(tmp1))) &&
hasBitWidth(tmp0, 16) &&
hasBitWidth(tmp1, 16);
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation35;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1;
    bool Matched = hasBitWidth(V, 32) &&
PatternMatch::match(V, m_c_Mul(
      m_Value(tmp0),
      m_Value(tmp1))) &&
hasBitWidth(tmp0, 32) &&
hasBitWidth(tmp1, 32);
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation36;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1;
    bool Matched = hasBitWidth(V, 32) &&
PatternMatch::match(V, m_c_FMul(
      m_Value(tmp0),
      m_Value(tmp1))) &&
hasBitWidth(tmp0, 32) &&
hasBitWidth(tmp1, 32);
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation37;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1;
    bool Matched = hasBitWidth(V, 16) &&
PatternMatch::match(V, m_c_Mul(
      m_SExt(
        m_Value(tmp0)),
      m_SExt(
        m_Value(tmp1)))) &&
hasBitWidth(tmp0, 8) &&
hasBitWidth(tmp1, 8);
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation38;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1;
    bool Matched = hasBitWidth(V, 32) &&
PatternMatch::match(V, m_c_Mul(
      m_SExt(
        m_Value(tmp0)),
      m_SExt(
        m_Value(tmp1)))) &&
hasBitWidth(tmp0, 16) &&
hasBitWidth(tmp1, 16);
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation39;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1;
    bool Matched = hasBitWidth(V, 64) &&
PatternMatch::match(V, m_c_Mul(
      m_SExt(
        m_Value(tmp0)),
      m_SExt(
        m_Value(tmp1)))) &&
hasBitWidth(tmp0, 32) &&
hasBitWidth(tmp1, 32);
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation40;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1;
    bool Matched = hasBitWidth(V, 16) &&
PatternMatch::match(V, m_c_Mul(
      m_ZExt(
        m_Value(tmp0)),
      m_ZExt(
        m_Value(tmp1)))) &&
hasBitWidth(tmp0, 8) &&
hasBitWidth(tmp1, 8);
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation41;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1;
    bool Matched = hasBitWidth(V, 32) &&
PatternMatch::match(V, m_c_Mul(
      m_ZExt(
        m_Value(tmp0)),
      m_ZExt(
        m_Value(tmp1)))) &&
hasBitWidth(tmp0, 16) &&
hasBitWidth(tmp1, 16);
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation42;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1;
    bool Matched = hasBitWidth(V, 64) &&
PatternMatch::match(V, m_c_Mul(
      m_ZExt(
        m_Value(tmp0)),
      m_ZExt(
        m_Value(tmp1)))) &&
hasBitWidth(tmp0, 32) &&
hasBitWidth(tmp1, 32);
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation43;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1; Value *tmp2;
    bool Matched = hasBitWidth(V, 8) &&
PatternMatch::match(V, m_c_Add(
      m_c_Mul(
        m_Value(tmp0),
        m_Value(tmp1)),
      m_Value(tmp2))) &&
hasBitWidth(tmp0, 8) &&
hasBitWidth(tmp1, 8) &&
hasBitWidth(tmp2, 8);
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1, tmp2 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation44;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1; Value *tmp2;
    bool Matched = hasBitWidth(V, 16) &&
PatternMatch::match(V, m_c_Add(
      m_c_Mul(
        m_Value(tmp0),
        m_Value(tmp1)),
      m_Value(tmp2))) &&
hasBitWidth(tmp0, 16) &&
hasBitWidth(tmp1, 16) &&
hasBitWidth(tmp2, 16);
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1, tmp2 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation45;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1; Value *tmp2;
    bool Matched = hasBitWidth(V, 32) &&
PatternMatch::match(V, m_c_Add(
      m_c_Mul(
        m_Value(tmp0),
        m_Value(tmp1)),
      m_Value(tmp2))) &&
hasBitWidth(tmp0, 32) &&
hasBitWidth(tmp1, 32) &&
hasBitWidth(tmp2, 32);
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1, tmp2 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation46;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1; Value *tmp2;
    bool Matched = hasBitWidth(V, 32) &&
PatternMatch::match(V, m_c_FAdd(
      m_Value(tmp0),
      m_c_FMul(
        m_Value(tmp1),
        m_Value(tmp2)))) &&
hasBitWidth(tmp0, 32) &&
hasBitWidth(tmp1, 32) &&
hasBitWidth(tmp2, 32);
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1, tmp2 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation47;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1; Value *tmp2;
    bool Matched = hasBitWidth(V, 16) &&
PatternMatch::match(V, m_c_Add(
      m_c_Mul(
        m_SExt(
          m_Value(tmp0)),
        m_SExt(
          m_Value(tmp1))),
      m_Value(tmp2))) &&
hasBitWidth(tmp0, 8) &&
hasBitWidth(tmp1, 8) &&
hasBitWidth(tmp2, 16);
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1, tmp2 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation48;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1; Value *tmp2;
    bool Matched = hasBitWidth(V, 32) &&
PatternMatch::match(V, m_c_Add(
      m_c_Mul(
        m_SExt(
          m_Value(tmp0)),
        m_SExt(
          m_Value(tmp1))),
      m_Value(tmp2))) &&
hasBitWidth(tmp0, 16) &&
hasBitWidth(tmp1, 16) &&
hasBitWidth(tmp2, 32);
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1, tmp2 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation49;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1; Value *tmp2;
    bool Matched = hasBitWidth(V, 64) &&
PatternMatch::match(V, m_c_Add(
      m_c_Mul(
        m_SExt(
          m_Value(tmp0)),
        m_SExt(
          m_Value(tmp1))),
      m_Value(tmp2))) &&
hasBitWidth(tmp0, 32) &&
hasBitWidth(tmp1, 32) &&
hasBitWidth(tmp2, 64);
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1, tmp2 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation50;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1; Value *tmp2;
    bool Matched = hasBitWidth(V, 16) &&
PatternMatch::match(V, m_c_Add(
      m_c_Mul(
        m_ZExt(
          m_Value(tmp0)),
        m_ZExt(
          m_Value(tmp1))),
      m_Value(tmp2))) &&
hasBitWidth(tmp0, 8) &&
hasBitWidth(tmp1, 8) &&
hasBitWidth(tmp2, 16);
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1, tmp2 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation51;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1; Value *tmp2;
    bool Matched = hasBitWidth(V, 32) &&
PatternMatch::match(V, m_c_Add(
      m_c_Mul(
        m_ZExt(
          m_Value(tmp0)),
        m_ZExt(
          m_Value(tmp1))),
      m_Value(tmp2))) &&
hasBitWidth(tmp0, 16) &&
hasBitWidth(tmp1, 16) &&
hasBitWidth(tmp2, 32);
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1, tmp2 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation52;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1; Value *tmp2;
    bool Matched = hasBitWidth(V, 64) &&
PatternMatch::match(V, m_c_Add(
      m_c_Mul(
        m_ZExt(
          m_Value(tmp0)),
        m_ZExt(
          m_Value(tmp1))),
      m_Value(tmp2))) &&
hasBitWidth(tmp0, 32) &&
hasBitWidth(tmp1, 32) &&
hasBitWidth(tmp2, 64);
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1, tmp2 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation53;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1; Value *tmp2;
    bool Matched = hasBitWidth(V, 8) &&
PatternMatch::match(V, m_Sub(
      m_Value(tmp0),
      m_c_Mul(
        m_Value(tmp1),
        m_Value(tmp2)))) &&
hasBitWidth(tmp0, 8) &&
hasBitWidth(tmp1, 8) &&
hasBitWidth(tmp2, 8);
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1, tmp2 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation54;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1; Value *tmp2;
    bool Matched = hasBitWidth(V, 16) &&
PatternMatch::match(V, m_Sub(
      m_Value(tmp0),
      m_c_Mul(
        m_Value(tmp1),
        m_Value(tmp2)))) &&
hasBitWidth(tmp0, 16) &&
hasBitWidth(tmp1, 16) &&
hasBitWidth(tmp2, 16);
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1, tmp2 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation55;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1; Value *tmp2;
    bool Matched = hasBitWidth(V, 32) &&
PatternMatch::match(V, m_Sub(
      m_Value(tmp0),
      m_c_Mul(
        m_Value(tmp1),
        m_Value(tmp2)))) &&
hasBitWidth(tmp0, 32) &&
hasBitWidth(tmp1, 32) &&
hasBitWidth(tmp2, 32);
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1, tmp2 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation56;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1; Value *tmp2;
    bool Matched = hasBitWidth(V, 32) &&
PatternMatch::match(V, m_FSub(
      m_Value(tmp0),
      m_c_FMul(
        m_Value(tmp1),
        m_Value(tmp2)))) &&
hasBitWidth(tmp0, 32) &&
hasBitWidth(tmp1, 32) &&
hasBitWidth(tmp2, 32);
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1, tmp2 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation57;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1; Value *tmp2;
    bool Matched = hasBitWidth(V, 16) &&
PatternMatch::match(V, m_Sub(
      m_Value(tmp0),
      m_c_Mul(
        m_SExt(
          m_Value(tmp1)),
        m_SExt(
          m_Value(tmp2))))) &&
hasBitWidth(tmp0, 16) &&
hasBitWidth(tmp1, 8) &&
hasBitWidth(tmp2, 8);
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1, tmp2 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation58;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1; Value *tmp2;
    bool Matched = hasBitWidth(V, 32) &&
PatternMatch::match(V, m_Sub(
      m_Value(tmp0),
      m_c_Mul(
        m_SExt(
          m_Value(tmp1)),
        m_SExt(
          m_Value(tmp2))))) &&
hasBitWidth(tmp0, 32) &&
hasBitWidth(tmp1, 16) &&
hasBitWidth(tmp2, 16);
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1, tmp2 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation59;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1; Value *tmp2;
    bool Matched = hasBitWidth(V, 64) &&
PatternMatch::match(V, m_Sub(
      m_Value(tmp0),
      m_c_Mul(
        m_SExt(
          m_Value(tmp1)),
        m_SExt(
          m_Value(tmp2))))) &&
hasBitWidth(tmp0, 64) &&
hasBitWidth(tmp1, 32) &&
hasBitWidth(tmp2, 32);
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1, tmp2 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation60;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1; Value *tmp2;
    bool Matched = hasBitWidth(V, 16) &&
PatternMatch::match(V, m_Sub(
      m_Value(tmp0),
      m_c_Mul(
        m_ZExt(
          m_Value(tmp1)),
        m_ZExt(
          m_Value(tmp2))))) &&
hasBitWidth(tmp0, 16) &&
hasBitWidth(tmp1, 8) &&
hasBitWidth(tmp2, 8);
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1, tmp2 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation61;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1; Value *tmp2;
    bool Matched = hasBitWidth(V, 32) &&
PatternMatch::match(V, m_Sub(
      m_Value(tmp0),
      m_c_Mul(
        m_ZExt(
          m_Value(tmp1)),
        m_ZExt(
          m_Value(tmp2))))) &&
hasBitWidth(tmp0, 32) &&
hasBitWidth(tmp1, 16) &&
hasBitWidth(tmp2, 16);
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1, tmp2 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation62;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1; Value *tmp2;
    bool Matched = hasBitWidth(V, 64) &&
PatternMatch::match(V, m_Sub(
      m_Value(tmp0),
      m_c_Mul(
        m_ZExt(
          m_Value(tmp1)),
        m_ZExt(
          m_Value(tmp2))))) &&
hasBitWidth(tmp0, 64) &&
hasBitWidth(tmp1, 32) &&
hasBitWidth(tmp2, 32);
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1, tmp2 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation63;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1; Value *tmp2; Value *tmp3;
    bool Matched = hasBitWidth(V, 16) &&
PatternMatch::match(V, m_Trunc(
      m_SelectOnCmp(CmpInst::Predicate::ICMP_SLT,
        m_Shl(
          m_c_Mul(
            m_SExt(
              m_Value(tmp0)),
            m_SExt(
              m_Value(tmp1))),
          m_SpecificInt(APInt(32, "1", 10))),
        m_SpecificInt(APInt(32, "-2147418112", 10)),
        m_SpecificInt(APInt(32, "32768", 10)),
        m_LShr(
          m_c_Mul(
            m_SExt(
              m_Value(tmp2)),
            m_SExt(
              m_Value(tmp3))),
          m_SpecificInt(APInt(32, "15", 10)))))) &&
hasBitWidth(tmp0, 16) &&
tmp0 == tmp2 &&
hasBitWidth(tmp1, 16) &&
tmp1 == tmp3;
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation64;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1; Value *tmp2; Value *tmp3;
    bool Matched = hasBitWidth(V, 32) &&
PatternMatch::match(V, m_Trunc(
      m_SelectOnCmp(CmpInst::Predicate::ICMP_SLT,
        m_Shl(
          m_c_Mul(
            m_SExt(
              m_Value(tmp0)),
            m_SExt(
              m_Value(tmp1))),
          m_SpecificInt(APInt(64, "1", 10))),
        m_SpecificInt(APInt(64, "-9223372032559808512", 10)),
        m_SpecificInt(APInt(64, "2147483648", 10)),
        m_LShr(
          m_c_Mul(
            m_SExt(
              m_Value(tmp2)),
            m_SExt(
              m_Value(tmp3))),
          m_SpecificInt(APInt(64, "31", 10)))))) &&
hasBitWidth(tmp0, 32) &&
tmp0 == tmp2 &&
hasBitWidth(tmp1, 32) &&
tmp1 == tmp3;
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation65;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1; Value *tmp2; Value *tmp3;
    bool Matched = hasBitWidth(V, 16) &&
PatternMatch::match(V, m_Trunc(
      m_SelectOnCmp(CmpInst::Predicate::ICMP_SLT,
        m_c_Add(
          m_c_Mul(
            m_Shl(
              m_SExt(
                m_Value(tmp0)),
              m_SpecificInt(APInt(32, "1", 10))),
            m_SExt(
              m_Value(tmp1))),
          m_SpecificInt(APInt(32, "32768", 10))),
        m_SpecificInt(APInt(32, "-2147418112", 10)),
        m_SpecificInt(APInt(32, "32768", 10)),
        m_LShr(
          m_c_Add(
            m_c_Mul(
              m_Shl(
                m_SExt(
                  m_Value(tmp2)),
                m_SpecificInt(APInt(32, "1", 10))),
              m_SExt(
                m_Value(tmp3))),
            m_SpecificInt(APInt(32, "32768", 10))),
          m_SpecificInt(APInt(32, "16", 10)))))) &&
hasBitWidth(tmp0, 16) &&
tmp0 == tmp2 &&
hasBitWidth(tmp1, 16) &&
tmp1 == tmp3;
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation66;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1; Value *tmp2; Value *tmp3;
    bool Matched = hasBitWidth(V, 32) &&
PatternMatch::match(V, m_Trunc(
      m_SelectOnCmp(CmpInst::Predicate::ICMP_SLT,
        m_c_Add(
          m_c_Mul(
            m_Shl(
              m_SExt(
                m_Value(tmp0)),
              m_SpecificInt(APInt(64, "1", 10))),
            m_SExt(
              m_Value(tmp1))),
          m_SpecificInt(APInt(64, "2147483648", 10))),
        m_SpecificInt(APInt(64, "-9223372032559808512", 10)),
        m_SpecificInt(APInt(64, "2147483648", 10)),
        m_LShr(
          m_c_Add(
            m_c_Mul(
              m_Shl(
                m_SExt(
                  m_Value(tmp2)),
                m_SpecificInt(APInt(64, "1", 10))),
              m_SExt(
                m_Value(tmp3))),
            m_SpecificInt(APInt(64, "2147483648", 10))),
          m_SpecificInt(APInt(64, "32", 10)))))) &&
hasBitWidth(tmp0, 32) &&
tmp0 == tmp2 &&
hasBitWidth(tmp1, 32) &&
tmp1 == tmp3;
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation67;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1;
    bool Matched = hasBitWidth(V, 8) &&
PatternMatch::match(V, m_Sub(
      m_Value(tmp0),
      m_Value(tmp1))) &&
hasBitWidth(tmp0, 8) &&
hasBitWidth(tmp1, 8);
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation68;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1;
    bool Matched = hasBitWidth(V, 16) &&
PatternMatch::match(V, m_Sub(
      m_Value(tmp0),
      m_Value(tmp1))) &&
hasBitWidth(tmp0, 16) &&
hasBitWidth(tmp1, 16);
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation69;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1;
    bool Matched = hasBitWidth(V, 32) &&
PatternMatch::match(V, m_Sub(
      m_Value(tmp0),
      m_Value(tmp1))) &&
hasBitWidth(tmp0, 32) &&
hasBitWidth(tmp1, 32);
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation70;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1;
    bool Matched = hasBitWidth(V, 64) &&
PatternMatch::match(V, m_Sub(
      m_Value(tmp0),
      m_Value(tmp1))) &&
hasBitWidth(tmp0, 64) &&
hasBitWidth(tmp1, 64);
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation71;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1;
    bool Matched = hasBitWidth(V, 32) &&
PatternMatch::match(V, m_FSub(
      m_Value(tmp0),
      m_Value(tmp1))) &&
hasBitWidth(tmp0, 32) &&
hasBitWidth(tmp1, 32);
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation72;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1;
    bool Matched = hasBitWidth(V, 16) &&
PatternMatch::match(V, m_Sub(
      m_SExt(
        m_Value(tmp0)),
      m_SExt(
        m_Value(tmp1)))) &&
hasBitWidth(tmp0, 8) &&
hasBitWidth(tmp1, 8);
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation73;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1;
    bool Matched = hasBitWidth(V, 32) &&
PatternMatch::match(V, m_Sub(
      m_SExt(
        m_Value(tmp0)),
      m_SExt(
        m_Value(tmp1)))) &&
hasBitWidth(tmp0, 16) &&
hasBitWidth(tmp1, 16);
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation74;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1;
    bool Matched = hasBitWidth(V, 64) &&
PatternMatch::match(V, m_Sub(
      m_SExt(
        m_Value(tmp0)),
      m_SExt(
        m_Value(tmp1)))) &&
hasBitWidth(tmp0, 32) &&
hasBitWidth(tmp1, 32);
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation75;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1;
    bool Matched = hasBitWidth(V, 16) &&
PatternMatch::match(V, m_Sub(
      m_ZExt(
        m_Value(tmp0)),
      m_ZExt(
        m_Value(tmp1)))) &&
hasBitWidth(tmp0, 8) &&
hasBitWidth(tmp1, 8);
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation76;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1;
    bool Matched = hasBitWidth(V, 32) &&
PatternMatch::match(V, m_Sub(
      m_ZExt(
        m_Value(tmp0)),
      m_ZExt(
        m_Value(tmp1)))) &&
hasBitWidth(tmp0, 16) &&
hasBitWidth(tmp1, 16);
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation77;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1;
    bool Matched = hasBitWidth(V, 64) &&
PatternMatch::match(V, m_Sub(
      m_ZExt(
        m_Value(tmp0)),
      m_ZExt(
        m_Value(tmp1)))) &&
hasBitWidth(tmp0, 32) &&
hasBitWidth(tmp1, 32);
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation78;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1;
    bool Matched = hasBitWidth(V, 16) &&
PatternMatch::match(V, m_Sub(
      m_Value(tmp0),
      m_SExt(
        m_Value(tmp1)))) &&
hasBitWidth(tmp0, 16) &&
hasBitWidth(tmp1, 8);
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation79;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1;
    bool Matched = hasBitWidth(V, 32) &&
PatternMatch::match(V, m_Sub(
      m_Value(tmp0),
      m_SExt(
        m_Value(tmp1)))) &&
hasBitWidth(tmp0, 32) &&
hasBitWidth(tmp1, 16);
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation80;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1;
    bool Matched = hasBitWidth(V, 64) &&
PatternMatch::match(V, m_Sub(
      m_Value(tmp0),
      m_SExt(
        m_Value(tmp1)))) &&
hasBitWidth(tmp0, 64) &&
hasBitWidth(tmp1, 32);
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation81;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1;
    bool Matched = hasBitWidth(V, 16) &&
PatternMatch::match(V, m_Sub(
      m_Value(tmp0),
      m_ZExt(
        m_Value(tmp1)))) &&
hasBitWidth(tmp0, 16) &&
hasBitWidth(tmp1, 8);
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation82;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1;
    bool Matched = hasBitWidth(V, 32) &&
PatternMatch::match(V, m_Sub(
      m_Value(tmp0),
      m_ZExt(
        m_Value(tmp1)))) &&
hasBitWidth(tmp0, 32) &&
hasBitWidth(tmp1, 16);
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation83;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1;
    bool Matched = hasBitWidth(V, 64) &&
PatternMatch::match(V, m_Sub(
      m_Value(tmp0),
      m_ZExt(
        m_Value(tmp1)))) &&
hasBitWidth(tmp0, 64) &&
hasBitWidth(tmp1, 32);
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation84;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1; Value *tmp2; Value *tmp3; Value *tmp4; Value *tmp5;
    bool Matched = hasBitWidth(V, 8) &&
PatternMatch::match(V, m_Trunc(
      m_SelectOnCmp(CmpInst::Predicate::ICMP_SGT,
        m_Sub(
          m_SExt(
            m_Value(tmp0)),
          m_SExt(
            m_Value(tmp1))),
        m_SpecificInt(APInt(16, "127", 10)),
        m_SpecificInt(APInt(16, "127", 10)),
        m_SelectOnCmp(CmpInst::Predicate::ICMP_SLT,
          m_Sub(
            m_SExt(
              m_Value(tmp2)),
            m_SExt(
              m_Value(tmp3))),
          m_SpecificInt(APInt(16, "65409", 10)),
          m_SpecificInt(APInt(16, "65408", 10)),
          m_Sub(
            m_SExt(
              m_Value(tmp4)),
            m_SExt(
              m_Value(tmp5))))))) &&
hasBitWidth(tmp0, 8) &&
tmp0 == tmp2 &&
tmp0 == tmp4 &&
hasBitWidth(tmp1, 8) &&
tmp1 == tmp3 &&
tmp1 == tmp5;
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation85;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1; Value *tmp2; Value *tmp3; Value *tmp4; Value *tmp5;
    bool Matched = hasBitWidth(V, 16) &&
PatternMatch::match(V, m_Trunc(
      m_SelectOnCmp(CmpInst::Predicate::ICMP_SGT,
        m_Sub(
          m_SExt(
            m_Value(tmp0)),
          m_SExt(
            m_Value(tmp1))),
        m_SpecificInt(APInt(32, "32767", 10)),
        m_SpecificInt(APInt(32, "32767", 10)),
        m_SelectOnCmp(CmpInst::Predicate::ICMP_SLT,
          m_Sub(
            m_SExt(
              m_Value(tmp2)),
            m_SExt(
              m_Value(tmp3))),
          m_SpecificInt(APInt(32, "4294934529", 10)),
          m_SpecificInt(APInt(32, "4294934528", 10)),
          m_Sub(
            m_SExt(
              m_Value(tmp4)),
            m_SExt(
              m_Value(tmp5))))))) &&
hasBitWidth(tmp0, 16) &&
tmp0 == tmp2 &&
tmp0 == tmp4 &&
hasBitWidth(tmp1, 16) &&
tmp1 == tmp3 &&
tmp1 == tmp5;
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation86;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1; Value *tmp2; Value *tmp3; Value *tmp4; Value *tmp5;
    bool Matched = hasBitWidth(V, 32) &&
PatternMatch::match(V, m_Trunc(
      m_SelectOnCmp(CmpInst::Predicate::ICMP_SGT,
        m_Sub(
          m_SExt(
            m_Value(tmp0)),
          m_SExt(
            m_Value(tmp1))),
        m_SpecificInt(APInt(64, "2147483647", 10)),
        m_SpecificInt(APInt(64, "2147483647", 10)),
        m_SelectOnCmp(CmpInst::Predicate::ICMP_SLT,
          m_Sub(
            m_SExt(
              m_Value(tmp2)),
            m_SExt(
              m_Value(tmp3))),
          m_SpecificInt(APInt(64, "18446744071562067969", 10)),
          m_SpecificInt(APInt(64, "18446744071562067968", 10)),
          m_Sub(
            m_SExt(
              m_Value(tmp4)),
            m_SExt(
              m_Value(tmp5))))))) &&
hasBitWidth(tmp0, 32) &&
tmp0 == tmp2 &&
tmp0 == tmp4 &&
hasBitWidth(tmp1, 32) &&
tmp1 == tmp3 &&
tmp1 == tmp5;
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation87;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1; Value *tmp2; Value *tmp3;
    bool Matched = hasBitWidth(V, 8) &&
PatternMatch::match(V, m_Trunc(
      m_SelectOnCmp(CmpInst::Predicate::ICMP_ULT,
        m_Sub(
          m_ZExt(
            m_Value(tmp0)),
          m_ZExt(
            m_Value(tmp1))),
        m_SpecificInt(APInt(16, "255", 10)),
        m_Sub(
          m_ZExt(
            m_Value(tmp2)),
          m_ZExt(
            m_Value(tmp3))),
        m_SpecificInt(APInt(16, "255", 10))))) &&
hasBitWidth(tmp0, 8) &&
tmp0 == tmp2 &&
hasBitWidth(tmp1, 8) &&
tmp1 == tmp3;
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation88;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1; Value *tmp2; Value *tmp3;
    bool Matched = hasBitWidth(V, 16) &&
PatternMatch::match(V, m_Trunc(
      m_SelectOnCmp(CmpInst::Predicate::ICMP_ULT,
        m_Sub(
          m_ZExt(
            m_Value(tmp0)),
          m_ZExt(
            m_Value(tmp1))),
        m_SpecificInt(APInt(32, "65535", 10)),
        m_Sub(
          m_ZExt(
            m_Value(tmp2)),
          m_ZExt(
            m_Value(tmp3))),
        m_SpecificInt(APInt(32, "65535", 10))))) &&
hasBitWidth(tmp0, 16) &&
tmp0 == tmp2 &&
hasBitWidth(tmp1, 16) &&
tmp1 == tmp3;
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation89;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1; Value *tmp2; Value *tmp3;
    bool Matched = hasBitWidth(V, 32) &&
PatternMatch::match(V, m_Trunc(
      m_SelectOnCmp(CmpInst::Predicate::ICMP_ULT,
        m_Sub(
          m_ZExt(
            m_Value(tmp0)),
          m_ZExt(
            m_Value(tmp1))),
        m_SpecificInt(APInt(64, "4294967295", 10)),
        m_Sub(
          m_ZExt(
            m_Value(tmp2)),
          m_ZExt(
            m_Value(tmp3))),
        m_SpecificInt(APInt(64, "4294967295", 10))))) &&
hasBitWidth(tmp0, 32) &&
tmp0 == tmp2 &&
hasBitWidth(tmp1, 32) &&
tmp1 == tmp3;
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation90;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1;
    bool Matched = hasBitWidth(V, 8) &&
PatternMatch::match(V, m_Trunc(
      m_LShr(
        m_Sub(
          m_SExt(
            m_Value(tmp0)),
          m_SExt(
            m_Value(tmp1))),
        m_SpecificInt(APInt(16, "1", 10))))) &&
hasBitWidth(tmp0, 8) &&
hasBitWidth(tmp1, 8);
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation91;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1;
    bool Matched = hasBitWidth(V, 16) &&
PatternMatch::match(V, m_Trunc(
      m_LShr(
        m_Sub(
          m_SExt(
            m_Value(tmp0)),
          m_SExt(
            m_Value(tmp1))),
        m_SpecificInt(APInt(32, "1", 10))))) &&
hasBitWidth(tmp0, 16) &&
hasBitWidth(tmp1, 16);
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation92;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1;
    bool Matched = hasBitWidth(V, 32) &&
PatternMatch::match(V, m_Trunc(
      m_LShr(
        m_Sub(
          m_SExt(
            m_Value(tmp0)),
          m_SExt(
            m_Value(tmp1))),
        m_SpecificInt(APInt(64, "1", 10))))) &&
hasBitWidth(tmp0, 32) &&
hasBitWidth(tmp1, 32);
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation93;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1;
    bool Matched = hasBitWidth(V, 8) &&
PatternMatch::match(V, m_Trunc(
      m_LShr(
        m_Sub(
          m_ZExt(
            m_Value(tmp0)),
          m_ZExt(
            m_Value(tmp1))),
        m_SpecificInt(APInt(16, "1", 10))))) &&
hasBitWidth(tmp0, 8) &&
hasBitWidth(tmp1, 8);
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation94;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1;
    bool Matched = hasBitWidth(V, 16) &&
PatternMatch::match(V, m_Trunc(
      m_LShr(
        m_Sub(
          m_ZExt(
            m_Value(tmp0)),
          m_ZExt(
            m_Value(tmp1))),
        m_SpecificInt(APInt(32, "1", 10))))) &&
hasBitWidth(tmp0, 16) &&
hasBitWidth(tmp1, 16);
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation95;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1;
    bool Matched = hasBitWidth(V, 32) &&
PatternMatch::match(V, m_Trunc(
      m_LShr(
        m_Sub(
          m_ZExt(
            m_Value(tmp0)),
          m_ZExt(
            m_Value(tmp1))),
        m_SpecificInt(APInt(64, "1", 10))))) &&
hasBitWidth(tmp0, 32) &&
hasBitWidth(tmp1, 32);
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation96;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1;
    bool Matched = hasBitWidth(V, 8) &&
PatternMatch::match(V, m_Trunc(
      m_LShr(
        m_Sub(
          m_ZExt(
            m_Value(tmp0)),
          m_ZExt(
            m_Value(tmp1))),
        m_SpecificInt(APInt(32, "8", 10))))) &&
hasBitWidth(tmp0, 16) &&
hasBitWidth(tmp1, 16);
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation97;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1;
    bool Matched = hasBitWidth(V, 16) &&
PatternMatch::match(V, m_Trunc(
      m_LShr(
        m_Sub(
          m_ZExt(
            m_Value(tmp0)),
          m_ZExt(
            m_Value(tmp1))),
        m_SpecificInt(APInt(64, "16", 10))))) &&
hasBitWidth(tmp0, 32) &&
hasBitWidth(tmp1, 32);
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation98;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1;
    bool Matched = hasBitWidth(V, 8) &&
PatternMatch::match(V, m_Trunc(
      m_LShr(
        m_Sub(
          m_c_Add(
            m_ZExt(
              m_Value(tmp0)),
            m_SpecificInt(APInt(32, "128", 10))),
          m_ZExt(
            m_Value(tmp1))),
        m_SpecificInt(APInt(32, "8", 10))))) &&
hasBitWidth(tmp0, 16) &&
hasBitWidth(tmp1, 16);
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation99;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1;
    bool Matched = hasBitWidth(V, 16) &&
PatternMatch::match(V, m_Trunc(
      m_LShr(
        m_Sub(
          m_c_Add(
            m_ZExt(
              m_Value(tmp0)),
            m_SpecificInt(APInt(64, "32768", 10))),
          m_ZExt(
            m_Value(tmp1))),
        m_SpecificInt(APInt(64, "16", 10))))) &&
hasBitWidth(tmp0, 32) &&
hasBitWidth(tmp1, 32);
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation100;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1; Value *tmp2; Value *tmp3; Value *tmp4; Value *tmp5;
    bool Matched = hasBitWidth(V, 8) &&
PatternMatch::match(V, m_SelectOnCmp(CmpInst::Predicate::ICMP_SGT,
      m_Value(tmp0),
      m_Value(tmp1),
      m_Sub(
        m_Value(tmp2),
        m_Value(tmp3)),
      m_Sub(
        m_Value(tmp4),
        m_Value(tmp5)))) &&
hasBitWidth(tmp0, 8) &&
tmp0 == tmp2 &&
tmp0 == tmp5 &&
hasBitWidth(tmp1, 8) &&
tmp1 == tmp3 &&
tmp1 == tmp4;
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation101;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1; Value *tmp2; Value *tmp3; Value *tmp4; Value *tmp5;
    bool Matched = hasBitWidth(V, 16) &&
PatternMatch::match(V, m_SelectOnCmp(CmpInst::Predicate::ICMP_SGT,
      m_Value(tmp0),
      m_Value(tmp1),
      m_Sub(
        m_Value(tmp2),
        m_Value(tmp3)),
      m_Sub(
        m_Value(tmp4),
        m_Value(tmp5)))) &&
hasBitWidth(tmp0, 16) &&
tmp0 == tmp2 &&
tmp0 == tmp5 &&
hasBitWidth(tmp1, 16) &&
tmp1 == tmp3 &&
tmp1 == tmp4;
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation102;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1; Value *tmp2; Value *tmp3; Value *tmp4; Value *tmp5;
    bool Matched = hasBitWidth(V, 32) &&
PatternMatch::match(V, m_SelectOnCmp(CmpInst::Predicate::ICMP_SGT,
      m_Value(tmp0),
      m_Value(tmp1),
      m_Sub(
        m_Value(tmp2),
        m_Value(tmp3)),
      m_Sub(
        m_Value(tmp4),
        m_Value(tmp5)))) &&
hasBitWidth(tmp0, 32) &&
tmp0 == tmp2 &&
tmp0 == tmp5 &&
hasBitWidth(tmp1, 32) &&
tmp1 == tmp3 &&
tmp1 == tmp4;
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation103;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1; Value *tmp2; Value *tmp3; Value *tmp4; Value *tmp5;
    bool Matched = hasBitWidth(V, 8) &&
PatternMatch::match(V, m_SelectOnCmp(CmpInst::Predicate::ICMP_UGT,
      m_Value(tmp0),
      m_Value(tmp1),
      m_Sub(
        m_Value(tmp2),
        m_Value(tmp3)),
      m_Sub(
        m_Value(tmp4),
        m_Value(tmp5)))) &&
hasBitWidth(tmp0, 8) &&
tmp0 == tmp2 &&
tmp0 == tmp5 &&
hasBitWidth(tmp1, 8) &&
tmp1 == tmp3 &&
tmp1 == tmp4;
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation104;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1; Value *tmp2; Value *tmp3; Value *tmp4; Value *tmp5;
    bool Matched = hasBitWidth(V, 16) &&
PatternMatch::match(V, m_SelectOnCmp(CmpInst::Predicate::ICMP_UGT,
      m_Value(tmp0),
      m_Value(tmp1),
      m_Sub(
        m_Value(tmp2),
        m_Value(tmp3)),
      m_Sub(
        m_Value(tmp4),
        m_Value(tmp5)))) &&
hasBitWidth(tmp0, 16) &&
tmp0 == tmp2 &&
tmp0 == tmp5 &&
hasBitWidth(tmp1, 16) &&
tmp1 == tmp3 &&
tmp1 == tmp4;
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation105;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1; Value *tmp2; Value *tmp3; Value *tmp4; Value *tmp5;
    bool Matched = hasBitWidth(V, 32) &&
PatternMatch::match(V, m_SelectOnCmp(CmpInst::Predicate::ICMP_UGT,
      m_Value(tmp0),
      m_Value(tmp1),
      m_Sub(
        m_Value(tmp2),
        m_Value(tmp3)),
      m_Sub(
        m_Value(tmp4),
        m_Value(tmp5)))) &&
hasBitWidth(tmp0, 32) &&
tmp0 == tmp2 &&
tmp0 == tmp5 &&
hasBitWidth(tmp1, 32) &&
tmp1 == tmp3 &&
tmp1 == tmp4;
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation106;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1; Value *tmp2; Value *tmp3; Value *tmp4; Value *tmp5;
    bool Matched = hasBitWidth(V, 32) &&
PatternMatch::match(V, m_SelectOnCmp(CmpInst::Predicate::FCMP_OLT,
      m_Value(tmp0),
      m_Value(tmp1),
      m_FSub(
        m_Value(tmp2),
        m_Value(tmp3)),
      m_FSub(
        m_Value(tmp4),
        m_Value(tmp5)))) &&
hasBitWidth(tmp0, 32) &&
tmp0 == tmp3 &&
tmp0 == tmp4 &&
hasBitWidth(tmp1, 32) &&
tmp1 == tmp2 &&
tmp1 == tmp5;
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation107;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1; Value *tmp2; Value *tmp3; Value *tmp4; Value *tmp5;
    bool Matched = hasBitWidth(V, 16) &&
PatternMatch::match(V, m_SelectOnCmp(CmpInst::Predicate::ICMP_SGT,
      m_Value(tmp0),
      m_Value(tmp1),
      m_Sub(
        m_SExt(
          m_Value(tmp2)),
        m_SExt(
          m_Value(tmp3))),
      m_Sub(
        m_SExt(
          m_Value(tmp4)),
        m_SExt(
          m_Value(tmp5))))) &&
hasBitWidth(tmp0, 8) &&
tmp0 == tmp2 &&
tmp0 == tmp5 &&
hasBitWidth(tmp1, 8) &&
tmp1 == tmp3 &&
tmp1 == tmp4;
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation108;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1; Value *tmp2; Value *tmp3; Value *tmp4; Value *tmp5;
    bool Matched = hasBitWidth(V, 32) &&
PatternMatch::match(V, m_SelectOnCmp(CmpInst::Predicate::ICMP_SGT,
      m_Value(tmp0),
      m_Value(tmp1),
      m_Sub(
        m_SExt(
          m_Value(tmp2)),
        m_SExt(
          m_Value(tmp3))),
      m_Sub(
        m_SExt(
          m_Value(tmp4)),
        m_SExt(
          m_Value(tmp5))))) &&
hasBitWidth(tmp0, 16) &&
tmp0 == tmp2 &&
tmp0 == tmp5 &&
hasBitWidth(tmp1, 16) &&
tmp1 == tmp3 &&
tmp1 == tmp4;
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation109;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1; Value *tmp2; Value *tmp3; Value *tmp4; Value *tmp5;
    bool Matched = hasBitWidth(V, 64) &&
PatternMatch::match(V, m_SelectOnCmp(CmpInst::Predicate::ICMP_SGT,
      m_Value(tmp0),
      m_Value(tmp1),
      m_Sub(
        m_SExt(
          m_Value(tmp2)),
        m_SExt(
          m_Value(tmp3))),
      m_Sub(
        m_SExt(
          m_Value(tmp4)),
        m_SExt(
          m_Value(tmp5))))) &&
hasBitWidth(tmp0, 32) &&
tmp0 == tmp2 &&
tmp0 == tmp5 &&
hasBitWidth(tmp1, 32) &&
tmp1 == tmp3 &&
tmp1 == tmp4;
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation110;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1; Value *tmp2; Value *tmp3; Value *tmp4; Value *tmp5;
    bool Matched = hasBitWidth(V, 16) &&
PatternMatch::match(V, m_SelectOnCmp(CmpInst::Predicate::ICMP_UGT,
      m_Value(tmp0),
      m_Value(tmp1),
      m_Sub(
        m_ZExt(
          m_Value(tmp2)),
        m_ZExt(
          m_Value(tmp3))),
      m_Sub(
        m_ZExt(
          m_Value(tmp4)),
        m_ZExt(
          m_Value(tmp5))))) &&
hasBitWidth(tmp0, 8) &&
tmp0 == tmp2 &&
tmp0 == tmp5 &&
hasBitWidth(tmp1, 8) &&
tmp1 == tmp3 &&
tmp1 == tmp4;
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation111;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1; Value *tmp2; Value *tmp3; Value *tmp4; Value *tmp5;
    bool Matched = hasBitWidth(V, 32) &&
PatternMatch::match(V, m_SelectOnCmp(CmpInst::Predicate::ICMP_UGT,
      m_Value(tmp0),
      m_Value(tmp1),
      m_Sub(
        m_ZExt(
          m_Value(tmp2)),
        m_ZExt(
          m_Value(tmp3))),
      m_Sub(
        m_ZExt(
          m_Value(tmp4)),
        m_ZExt(
          m_Value(tmp5))))) &&
hasBitWidth(tmp0, 16) &&
tmp0 == tmp2 &&
tmp0 == tmp5 &&
hasBitWidth(tmp1, 16) &&
tmp1 == tmp3 &&
tmp1 == tmp4;
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation112;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1; Value *tmp2; Value *tmp3; Value *tmp4; Value *tmp5;
    bool Matched = hasBitWidth(V, 64) &&
PatternMatch::match(V, m_SelectOnCmp(CmpInst::Predicate::ICMP_UGT,
      m_Value(tmp0),
      m_Value(tmp1),
      m_Sub(
        m_ZExt(
          m_Value(tmp2)),
        m_ZExt(
          m_Value(tmp3))),
      m_Sub(
        m_ZExt(
          m_Value(tmp4)),
        m_ZExt(
          m_Value(tmp5))))) &&
hasBitWidth(tmp0, 32) &&
tmp0 == tmp2 &&
tmp0 == tmp5 &&
hasBitWidth(tmp1, 32) &&
tmp1 == tmp3 &&
tmp1 == tmp4;
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation113;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1; Value *tmp2; Value *tmp3; Value *tmp4; Value *tmp5; Value *tmp6;
    bool Matched = hasBitWidth(V, 8) &&
PatternMatch::match(V, m_c_Add(
      m_SelectOnCmp(CmpInst::Predicate::ICMP_SGT,
        m_Value(tmp0),
        m_Value(tmp1),
        m_Sub(
          m_Value(tmp2),
          m_Value(tmp3)),
        m_Sub(
          m_Value(tmp4),
          m_Value(tmp5))),
      m_Value(tmp6))) &&
hasBitWidth(tmp0, 8) &&
tmp0 == tmp2 &&
tmp0 == tmp5 &&
hasBitWidth(tmp1, 8) &&
tmp1 == tmp3 &&
tmp1 == tmp4 &&
hasBitWidth(tmp6, 8);
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1, tmp6 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation114;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1; Value *tmp2; Value *tmp3; Value *tmp4; Value *tmp5; Value *tmp6;
    bool Matched = hasBitWidth(V, 16) &&
PatternMatch::match(V, m_c_Add(
      m_SelectOnCmp(CmpInst::Predicate::ICMP_SGT,
        m_Value(tmp0),
        m_Value(tmp1),
        m_Sub(
          m_Value(tmp2),
          m_Value(tmp3)),
        m_Sub(
          m_Value(tmp4),
          m_Value(tmp5))),
      m_Value(tmp6))) &&
hasBitWidth(tmp0, 16) &&
tmp0 == tmp2 &&
tmp0 == tmp5 &&
hasBitWidth(tmp1, 16) &&
tmp1 == tmp3 &&
tmp1 == tmp4 &&
hasBitWidth(tmp6, 16);
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1, tmp6 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation115;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1; Value *tmp2; Value *tmp3; Value *tmp4; Value *tmp5; Value *tmp6;
    bool Matched = hasBitWidth(V, 32) &&
PatternMatch::match(V, m_c_Add(
      m_SelectOnCmp(CmpInst::Predicate::ICMP_SGT,
        m_Value(tmp0),
        m_Value(tmp1),
        m_Sub(
          m_Value(tmp2),
          m_Value(tmp3)),
        m_Sub(
          m_Value(tmp4),
          m_Value(tmp5))),
      m_Value(tmp6))) &&
hasBitWidth(tmp0, 32) &&
tmp0 == tmp2 &&
tmp0 == tmp5 &&
hasBitWidth(tmp1, 32) &&
tmp1 == tmp3 &&
tmp1 == tmp4 &&
hasBitWidth(tmp6, 32);
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1, tmp6 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation116;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1; Value *tmp2; Value *tmp3; Value *tmp4; Value *tmp5; Value *tmp6;
    bool Matched = hasBitWidth(V, 8) &&
PatternMatch::match(V, m_c_Add(
      m_SelectOnCmp(CmpInst::Predicate::ICMP_UGT,
        m_Value(tmp0),
        m_Value(tmp1),
        m_Sub(
          m_Value(tmp2),
          m_Value(tmp3)),
        m_Sub(
          m_Value(tmp4),
          m_Value(tmp5))),
      m_Value(tmp6))) &&
hasBitWidth(tmp0, 8) &&
tmp0 == tmp2 &&
tmp0 == tmp5 &&
hasBitWidth(tmp1, 8) &&
tmp1 == tmp3 &&
tmp1 == tmp4 &&
hasBitWidth(tmp6, 8);
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1, tmp6 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation117;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1; Value *tmp2; Value *tmp3; Value *tmp4; Value *tmp5; Value *tmp6;
    bool Matched = hasBitWidth(V, 16) &&
PatternMatch::match(V, m_c_Add(
      m_SelectOnCmp(CmpInst::Predicate::ICMP_UGT,
        m_Value(tmp0),
        m_Value(tmp1),
        m_Sub(
          m_Value(tmp2),
          m_Value(tmp3)),
        m_Sub(
          m_Value(tmp4),
          m_Value(tmp5))),
      m_Value(tmp6))) &&
hasBitWidth(tmp0, 16) &&
tmp0 == tmp2 &&
tmp0 == tmp5 &&
hasBitWidth(tmp1, 16) &&
tmp1 == tmp3 &&
tmp1 == tmp4 &&
hasBitWidth(tmp6, 16);
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1, tmp6 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation118;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1; Value *tmp2; Value *tmp3; Value *tmp4; Value *tmp5; Value *tmp6;
    bool Matched = hasBitWidth(V, 32) &&
PatternMatch::match(V, m_c_Add(
      m_SelectOnCmp(CmpInst::Predicate::ICMP_UGT,
        m_Value(tmp0),
        m_Value(tmp1),
        m_Sub(
          m_Value(tmp2),
          m_Value(tmp3)),
        m_Sub(
          m_Value(tmp4),
          m_Value(tmp5))),
      m_Value(tmp6))) &&
hasBitWidth(tmp0, 32) &&
tmp0 == tmp2 &&
tmp0 == tmp5 &&
hasBitWidth(tmp1, 32) &&
tmp1 == tmp3 &&
tmp1 == tmp4 &&
hasBitWidth(tmp6, 32);
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1, tmp6 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation119;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1; Value *tmp2; Value *tmp3; Value *tmp4; Value *tmp5; Value *tmp6;
    bool Matched = hasBitWidth(V, 16) &&
PatternMatch::match(V, m_c_Add(
      m_SelectOnCmp(CmpInst::Predicate::ICMP_SGT,
        m_Value(tmp0),
        m_Value(tmp1),
        m_Sub(
          m_SExt(
            m_Value(tmp2)),
          m_SExt(
            m_Value(tmp3))),
        m_Sub(
          m_SExt(
            m_Value(tmp4)),
          m_SExt(
            m_Value(tmp5)))),
      m_Value(tmp6))) &&
hasBitWidth(tmp0, 8) &&
tmp0 == tmp2 &&
tmp0 == tmp5 &&
hasBitWidth(tmp1, 8) &&
tmp1 == tmp3 &&
tmp1 == tmp4 &&
hasBitWidth(tmp6, 16);
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1, tmp6 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation120;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1; Value *tmp2; Value *tmp3; Value *tmp4; Value *tmp5; Value *tmp6;
    bool Matched = hasBitWidth(V, 32) &&
PatternMatch::match(V, m_c_Add(
      m_SelectOnCmp(CmpInst::Predicate::ICMP_SGT,
        m_Value(tmp0),
        m_Value(tmp1),
        m_Sub(
          m_SExt(
            m_Value(tmp2)),
          m_SExt(
            m_Value(tmp3))),
        m_Sub(
          m_SExt(
            m_Value(tmp4)),
          m_SExt(
            m_Value(tmp5)))),
      m_Value(tmp6))) &&
hasBitWidth(tmp0, 16) &&
tmp0 == tmp2 &&
tmp0 == tmp5 &&
hasBitWidth(tmp1, 16) &&
tmp1 == tmp3 &&
tmp1 == tmp4 &&
hasBitWidth(tmp6, 32);
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1, tmp6 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation121;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1; Value *tmp2; Value *tmp3; Value *tmp4; Value *tmp5; Value *tmp6;
    bool Matched = hasBitWidth(V, 64) &&
PatternMatch::match(V, m_c_Add(
      m_SelectOnCmp(CmpInst::Predicate::ICMP_SGT,
        m_Value(tmp0),
        m_Value(tmp1),
        m_Sub(
          m_SExt(
            m_Value(tmp2)),
          m_SExt(
            m_Value(tmp3))),
        m_Sub(
          m_SExt(
            m_Value(tmp4)),
          m_SExt(
            m_Value(tmp5)))),
      m_Value(tmp6))) &&
hasBitWidth(tmp0, 32) &&
tmp0 == tmp2 &&
tmp0 == tmp5 &&
hasBitWidth(tmp1, 32) &&
tmp1 == tmp3 &&
tmp1 == tmp4 &&
hasBitWidth(tmp6, 64);
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1, tmp6 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation122;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1; Value *tmp2; Value *tmp3; Value *tmp4; Value *tmp5; Value *tmp6;
    bool Matched = hasBitWidth(V, 16) &&
PatternMatch::match(V, m_c_Add(
      m_SelectOnCmp(CmpInst::Predicate::ICMP_UGT,
        m_Value(tmp0),
        m_Value(tmp1),
        m_Sub(
          m_ZExt(
            m_Value(tmp2)),
          m_ZExt(
            m_Value(tmp3))),
        m_Sub(
          m_ZExt(
            m_Value(tmp4)),
          m_ZExt(
            m_Value(tmp5)))),
      m_Value(tmp6))) &&
hasBitWidth(tmp0, 8) &&
tmp0 == tmp2 &&
tmp0 == tmp5 &&
hasBitWidth(tmp1, 8) &&
tmp1 == tmp3 &&
tmp1 == tmp4 &&
hasBitWidth(tmp6, 16);
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1, tmp6 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation123;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1; Value *tmp2; Value *tmp3; Value *tmp4; Value *tmp5; Value *tmp6;
    bool Matched = hasBitWidth(V, 32) &&
PatternMatch::match(V, m_c_Add(
      m_SelectOnCmp(CmpInst::Predicate::ICMP_UGT,
        m_Value(tmp0),
        m_Value(tmp1),
        m_Sub(
          m_ZExt(
            m_Value(tmp2)),
          m_ZExt(
            m_Value(tmp3))),
        m_Sub(
          m_ZExt(
            m_Value(tmp4)),
          m_ZExt(
            m_Value(tmp5)))),
      m_Value(tmp6))) &&
hasBitWidth(tmp0, 16) &&
tmp0 == tmp2 &&
tmp0 == tmp5 &&
hasBitWidth(tmp1, 16) &&
tmp1 == tmp3 &&
tmp1 == tmp4 &&
hasBitWidth(tmp6, 32);
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1, tmp6 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation124;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1; Value *tmp2; Value *tmp3; Value *tmp4; Value *tmp5; Value *tmp6;
    bool Matched = hasBitWidth(V, 64) &&
PatternMatch::match(V, m_c_Add(
      m_SelectOnCmp(CmpInst::Predicate::ICMP_UGT,
        m_Value(tmp0),
        m_Value(tmp1),
        m_Sub(
          m_ZExt(
            m_Value(tmp2)),
          m_ZExt(
            m_Value(tmp3))),
        m_Sub(
          m_ZExt(
            m_Value(tmp4)),
          m_ZExt(
            m_Value(tmp5)))),
      m_Value(tmp6))) &&
hasBitWidth(tmp0, 32) &&
tmp0 == tmp2 &&
tmp0 == tmp5 &&
hasBitWidth(tmp1, 32) &&
tmp1 == tmp3 &&
tmp1 == tmp4 &&
hasBitWidth(tmp6, 64);
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1, tmp6 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation125;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1; Value *tmp2; Value *tmp3;
    bool Matched = hasBitWidth(V, 8) &&
PatternMatch::match(V, m_SelectOnCmp(CmpInst::Predicate::ICMP_SGT,
      m_Value(tmp0),
      m_Value(tmp1),
      m_Value(tmp2),
      m_Value(tmp3))) &&
hasBitWidth(tmp0, 8) &&
tmp0 == tmp2 &&
hasBitWidth(tmp1, 8) &&
tmp1 == tmp3;
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation126;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1; Value *tmp2; Value *tmp3;
    bool Matched = hasBitWidth(V, 16) &&
PatternMatch::match(V, m_SelectOnCmp(CmpInst::Predicate::ICMP_SGT,
      m_Value(tmp0),
      m_Value(tmp1),
      m_Value(tmp2),
      m_Value(tmp3))) &&
hasBitWidth(tmp0, 16) &&
tmp0 == tmp2 &&
hasBitWidth(tmp1, 16) &&
tmp1 == tmp3;
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation127;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1; Value *tmp2; Value *tmp3;
    bool Matched = hasBitWidth(V, 32) &&
PatternMatch::match(V, m_SelectOnCmp(CmpInst::Predicate::ICMP_SGT,
      m_Value(tmp0),
      m_Value(tmp1),
      m_Value(tmp2),
      m_Value(tmp3))) &&
hasBitWidth(tmp0, 32) &&
tmp0 == tmp2 &&
hasBitWidth(tmp1, 32) &&
tmp1 == tmp3;
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation128;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1; Value *tmp2; Value *tmp3;
    bool Matched = hasBitWidth(V, 8) &&
PatternMatch::match(V, m_SelectOnCmp(CmpInst::Predicate::ICMP_UGT,
      m_Value(tmp0),
      m_Value(tmp1),
      m_Value(tmp2),
      m_Value(tmp3))) &&
hasBitWidth(tmp0, 8) &&
tmp0 == tmp2 &&
hasBitWidth(tmp1, 8) &&
tmp1 == tmp3;
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation129;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1; Value *tmp2; Value *tmp3;
    bool Matched = hasBitWidth(V, 16) &&
PatternMatch::match(V, m_SelectOnCmp(CmpInst::Predicate::ICMP_UGT,
      m_Value(tmp0),
      m_Value(tmp1),
      m_Value(tmp2),
      m_Value(tmp3))) &&
hasBitWidth(tmp0, 16) &&
tmp0 == tmp2 &&
hasBitWidth(tmp1, 16) &&
tmp1 == tmp3;
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation130;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1; Value *tmp2; Value *tmp3;
    bool Matched = hasBitWidth(V, 32) &&
PatternMatch::match(V, m_SelectOnCmp(CmpInst::Predicate::ICMP_UGT,
      m_Value(tmp0),
      m_Value(tmp1),
      m_Value(tmp2),
      m_Value(tmp3))) &&
hasBitWidth(tmp0, 32) &&
tmp0 == tmp2 &&
hasBitWidth(tmp1, 32) &&
tmp1 == tmp3;
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation131;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1; Value *tmp2; Value *tmp3;
    bool Matched = hasBitWidth(V, 32) &&
PatternMatch::match(V, m_SelectOnCmp(CmpInst::Predicate::FCMP_OLT,
      m_Value(tmp0),
      m_Value(tmp1),
      m_Value(tmp2),
      m_Value(tmp3))) &&
hasBitWidth(tmp0, 32) &&
tmp0 == tmp3 &&
hasBitWidth(tmp1, 32) &&
tmp1 == tmp2;
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation132;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1; Value *tmp2; Value *tmp3;
    bool Matched = hasBitWidth(V, 8) &&
PatternMatch::match(V, m_SelectOnCmp(CmpInst::Predicate::ICMP_SGT,
      m_Value(tmp0),
      m_Value(tmp1),
      m_Value(tmp2),
      m_Value(tmp3))) &&
hasBitWidth(tmp0, 8) &&
tmp0 == tmp3 &&
hasBitWidth(tmp1, 8) &&
tmp1 == tmp2;
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation133;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1; Value *tmp2; Value *tmp3;
    bool Matched = hasBitWidth(V, 16) &&
PatternMatch::match(V, m_SelectOnCmp(CmpInst::Predicate::ICMP_SGT,
      m_Value(tmp0),
      m_Value(tmp1),
      m_Value(tmp2),
      m_Value(tmp3))) &&
hasBitWidth(tmp0, 16) &&
tmp0 == tmp3 &&
hasBitWidth(tmp1, 16) &&
tmp1 == tmp2;
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation134;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1; Value *tmp2; Value *tmp3;
    bool Matched = hasBitWidth(V, 32) &&
PatternMatch::match(V, m_SelectOnCmp(CmpInst::Predicate::ICMP_SGT,
      m_Value(tmp0),
      m_Value(tmp1),
      m_Value(tmp2),
      m_Value(tmp3))) &&
hasBitWidth(tmp0, 32) &&
tmp0 == tmp3 &&
hasBitWidth(tmp1, 32) &&
tmp1 == tmp2;
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation135;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1; Value *tmp2; Value *tmp3;
    bool Matched = hasBitWidth(V, 8) &&
PatternMatch::match(V, m_SelectOnCmp(CmpInst::Predicate::ICMP_UGT,
      m_Value(tmp0),
      m_Value(tmp1),
      m_Value(tmp2),
      m_Value(tmp3))) &&
hasBitWidth(tmp0, 8) &&
tmp0 == tmp3 &&
hasBitWidth(tmp1, 8) &&
tmp1 == tmp2;
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation136;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1; Value *tmp2; Value *tmp3;
    bool Matched = hasBitWidth(V, 16) &&
PatternMatch::match(V, m_SelectOnCmp(CmpInst::Predicate::ICMP_UGT,
      m_Value(tmp0),
      m_Value(tmp1),
      m_Value(tmp2),
      m_Value(tmp3))) &&
hasBitWidth(tmp0, 16) &&
tmp0 == tmp3 &&
hasBitWidth(tmp1, 16) &&
tmp1 == tmp2;
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation137;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1; Value *tmp2; Value *tmp3;
    bool Matched = hasBitWidth(V, 32) &&
PatternMatch::match(V, m_SelectOnCmp(CmpInst::Predicate::ICMP_UGT,
      m_Value(tmp0),
      m_Value(tmp1),
      m_Value(tmp2),
      m_Value(tmp3))) &&
hasBitWidth(tmp0, 32) &&
tmp0 == tmp3 &&
hasBitWidth(tmp1, 32) &&
tmp1 == tmp2;
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation138;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1; Value *tmp2; Value *tmp3;
    bool Matched = hasBitWidth(V, 32) &&
PatternMatch::match(V, m_SelectOnCmp(CmpInst::Predicate::FCMP_OLT,
      m_Value(tmp0),
      m_Value(tmp1),
      m_Value(tmp2),
      m_Value(tmp3))) &&
hasBitWidth(tmp0, 32) &&
tmp0 == tmp2 &&
hasBitWidth(tmp1, 32) &&
tmp1 == tmp3;
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation139;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1;
    bool Matched = hasBitWidth(V, 8) &&
PatternMatch::match(V, m_c_Add(
      m_Value(tmp0),
      m_Value(tmp1))) &&
hasBitWidth(tmp0, 8) &&
hasBitWidth(tmp1, 8);
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation140;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1;
    bool Matched = hasBitWidth(V, 16) &&
PatternMatch::match(V, m_c_Add(
      m_Value(tmp0),
      m_Value(tmp1))) &&
hasBitWidth(tmp0, 16) &&
hasBitWidth(tmp1, 16);
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation141;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1;
    bool Matched = hasBitWidth(V, 32) &&
PatternMatch::match(V, m_c_Add(
      m_Value(tmp0),
      m_Value(tmp1))) &&
hasBitWidth(tmp0, 32) &&
hasBitWidth(tmp1, 32);
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation142;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1;
    bool Matched = hasBitWidth(V, 32) &&
PatternMatch::match(V, m_c_FAdd(
      m_Value(tmp0),
      m_Value(tmp1))) &&
hasBitWidth(tmp0, 32) &&
hasBitWidth(tmp1, 32);
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation143;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1; Value *tmp2;
    bool Matched = hasBitWidth(V, 16) &&
PatternMatch::match(V, m_c_Add(
      m_c_Add(
        m_SExt(
          m_Value(tmp0)),
        m_Value(tmp1)),
      m_SExt(
        m_Value(tmp2)))) &&
hasBitWidth(tmp0, 8) &&
hasBitWidth(tmp1, 16) &&
hasBitWidth(tmp2, 8);
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1, tmp2 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation144;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1; Value *tmp2;
    bool Matched = hasBitWidth(V, 32) &&
PatternMatch::match(V, m_c_Add(
      m_c_Add(
        m_SExt(
          m_Value(tmp0)),
        m_Value(tmp1)),
      m_SExt(
        m_Value(tmp2)))) &&
hasBitWidth(tmp0, 16) &&
hasBitWidth(tmp1, 32) &&
hasBitWidth(tmp2, 16);
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1, tmp2 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation145;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1; Value *tmp2;
    bool Matched = hasBitWidth(V, 64) &&
PatternMatch::match(V, m_c_Add(
      m_c_Add(
        m_SExt(
          m_Value(tmp0)),
        m_Value(tmp1)),
      m_SExt(
        m_Value(tmp2)))) &&
hasBitWidth(tmp0, 32) &&
hasBitWidth(tmp1, 64) &&
hasBitWidth(tmp2, 32);
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1, tmp2 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation146;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1; Value *tmp2;
    bool Matched = hasBitWidth(V, 16) &&
PatternMatch::match(V, m_c_Add(
      m_c_Add(
        m_ZExt(
          m_Value(tmp0)),
        m_Value(tmp1)),
      m_ZExt(
        m_Value(tmp2)))) &&
hasBitWidth(tmp0, 8) &&
hasBitWidth(tmp1, 16) &&
hasBitWidth(tmp2, 8);
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1, tmp2 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation147;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1; Value *tmp2;
    bool Matched = hasBitWidth(V, 32) &&
PatternMatch::match(V, m_c_Add(
      m_c_Add(
        m_ZExt(
          m_Value(tmp0)),
        m_Value(tmp1)),
      m_ZExt(
        m_Value(tmp2)))) &&
hasBitWidth(tmp0, 16) &&
hasBitWidth(tmp1, 32) &&
hasBitWidth(tmp2, 16);
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1, tmp2 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation148;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1; Value *tmp2;
    bool Matched = hasBitWidth(V, 64) &&
PatternMatch::match(V, m_c_Add(
      m_c_Add(
        m_ZExt(
          m_Value(tmp0)),
        m_Value(tmp1)),
      m_ZExt(
        m_Value(tmp2)))) &&
hasBitWidth(tmp0, 32) &&
hasBitWidth(tmp1, 64) &&
hasBitWidth(tmp2, 32);
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1, tmp2 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation149;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1; Value *tmp2; Value *tmp3; Value *tmp4; Value *tmp5; Value *tmp6; Value *tmp7; Value *tmp8;
    bool Matched = hasBitWidth(V, 32) &&
PatternMatch::match(V, m_c_Add(
      m_c_Add(
        m_c_Add(
          m_c_Add(
            m_c_Mul(
              m_ZExt(
                m_Value(tmp0)),
              m_ZExt(
                m_Value(tmp1))),
            m_Value(tmp2)),
          m_c_Mul(
            m_ZExt(
              m_Value(tmp3)),
            m_ZExt(
              m_Value(tmp4)))),
        m_c_Mul(
          m_ZExt(
            m_Value(tmp5)),
          m_ZExt(
            m_Value(tmp6)))),
      m_c_Mul(
        m_ZExt(
          m_Value(tmp7)),
        m_ZExt(
          m_Value(tmp8))))) &&
hasBitWidth(tmp0, 8) &&
hasBitWidth(tmp1, 8) &&
hasBitWidth(tmp2, 32) &&
hasBitWidth(tmp3, 8) &&
hasBitWidth(tmp4, 8) &&
hasBitWidth(tmp5, 8) &&
hasBitWidth(tmp6, 8) &&
hasBitWidth(tmp7, 8) &&
hasBitWidth(tmp8, 8);
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation150;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1; Value *tmp2; Value *tmp3; Value *tmp4; Value *tmp5; Value *tmp6; Value *tmp7; Value *tmp8;
    bool Matched = hasBitWidth(V, 32) &&
PatternMatch::match(V, m_c_Add(
      m_c_Add(
        m_c_Add(
          m_c_Add(
            m_c_Mul(
              m_SExt(
                m_Value(tmp0)),
              m_SExt(
                m_Value(tmp1))),
            m_Value(tmp2)),
          m_c_Mul(
            m_SExt(
              m_Value(tmp3)),
            m_SExt(
              m_Value(tmp4)))),
        m_c_Mul(
          m_SExt(
            m_Value(tmp5)),
          m_SExt(
            m_Value(tmp6)))),
      m_c_Mul(
        m_SExt(
          m_Value(tmp7)),
        m_SExt(
          m_Value(tmp8))))) &&
hasBitWidth(tmp0, 8) &&
hasBitWidth(tmp1, 8) &&
hasBitWidth(tmp2, 32) &&
hasBitWidth(tmp3, 8) &&
hasBitWidth(tmp4, 8) &&
hasBitWidth(tmp5, 8) &&
hasBitWidth(tmp6, 8) &&
hasBitWidth(tmp7, 8) &&
hasBitWidth(tmp8, 8);
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation151;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1; Value *tmp2; Value *tmp3; Value *tmp4; Value *tmp5; Value *tmp6; Value *tmp7; Value *tmp8;
    bool Matched = hasBitWidth(V, 32) &&
PatternMatch::match(V, m_c_Add(
      m_c_Add(
        m_c_Add(
          m_c_Add(
            m_c_Mul(
              m_SExt(
                m_Value(tmp0)),
              m_ZExt(
                m_Value(tmp1))),
            m_Value(tmp2)),
          m_c_Mul(
            m_SExt(
              m_Value(tmp3)),
            m_ZExt(
              m_Value(tmp4)))),
        m_c_Mul(
          m_SExt(
            m_Value(tmp5)),
          m_ZExt(
            m_Value(tmp6)))),
      m_c_Mul(
        m_SExt(
          m_Value(tmp7)),
        m_ZExt(
          m_Value(tmp8))))) &&
hasBitWidth(tmp0, 8) &&
hasBitWidth(tmp1, 8) &&
hasBitWidth(tmp2, 32) &&
hasBitWidth(tmp3, 8) &&
hasBitWidth(tmp4, 8) &&
hasBitWidth(tmp5, 8) &&
hasBitWidth(tmp6, 8) &&
hasBitWidth(tmp7, 8) &&
hasBitWidth(tmp8, 8);
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation152;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1; Value *tmp2; Value *tmp3; Value *tmp4; Value *tmp5; Value *tmp6; Value *tmp7; Value *tmp8; Value *tmp9; Value *tmp10; Value *tmp11; Value *tmp12; Value *tmp13; Value *tmp14;
    bool Matched = hasBitWidth(V, 32) &&
PatternMatch::match(V, m_c_Add(
      m_c_Add(
        m_c_Add(
          m_c_Add(
            m_c_Add(
              m_c_Add(
                m_c_Add(
                  m_c_Mul(
                    m_SExt(
                      m_Value(tmp0)),
                    m_SExt(
                      m_Value(tmp1))),
                  m_Value(tmp2)),
                m_c_Mul(
                  m_SExt(
                    m_Value(tmp3)),
                  m_SExt(
                    m_Value(tmp4)))),
              m_c_Mul(
                m_SExt(
                  m_Value(tmp5)),
                m_SExt(
                  m_Value(tmp6)))),
            m_c_Mul(
              m_SExt(
                m_Value(tmp7)),
              m_SExt(
                m_Value(tmp8)))),
          m_c_Mul(
            m_SExt(
              m_Value(tmp9)),
            m_SExt(
              m_Value(tmp10)))),
        m_c_Mul(
          m_SExt(
            m_Value(tmp11)),
          m_SExt(
            m_Value(tmp12)))),
      m_c_Mul(
        m_SExt(
          m_Value(tmp13)),
        m_SExt(
          m_Value(tmp14))))) &&
hasBitWidth(tmp0, 8) &&
hasBitWidth(tmp1, 8) &&
hasBitWidth(tmp2, 32) &&
hasBitWidth(tmp3, 8) &&
hasBitWidth(tmp4, 8) &&
hasBitWidth(tmp5, 8) &&
hasBitWidth(tmp6, 8) &&
hasBitWidth(tmp7, 8) &&
hasBitWidth(tmp8, 8) &&
hasBitWidth(tmp9, 8) &&
hasBitWidth(tmp10, 8) &&
hasBitWidth(tmp11, 8) &&
hasBitWidth(tmp12, 8) &&
hasBitWidth(tmp13, 8) &&
hasBitWidth(tmp14, 8);
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation153;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1; Value *tmp2; Value *tmp3; Value *tmp4; Value *tmp5; Value *tmp6; Value *tmp7; Value *tmp8; Value *tmp9; Value *tmp10; Value *tmp11; Value *tmp12; Value *tmp13; Value *tmp14;
    bool Matched = hasBitWidth(V, 32) &&
PatternMatch::match(V, m_c_Add(
      m_c_Add(
        m_c_Add(
          m_c_Add(
            m_c_Add(
              m_c_Add(
                m_c_Add(
                  m_c_Mul(
                    m_ZExt(
                      m_Value(tmp0)),
                    m_ZExt(
                      m_Value(tmp1))),
                  m_Value(tmp2)),
                m_c_Mul(
                  m_ZExt(
                    m_Value(tmp3)),
                  m_ZExt(
                    m_Value(tmp4)))),
              m_c_Mul(
                m_ZExt(
                  m_Value(tmp5)),
                m_ZExt(
                  m_Value(tmp6)))),
            m_c_Mul(
              m_ZExt(
                m_Value(tmp7)),
              m_ZExt(
                m_Value(tmp8)))),
          m_c_Mul(
            m_ZExt(
              m_Value(tmp9)),
            m_ZExt(
              m_Value(tmp10)))),
        m_c_Mul(
          m_ZExt(
            m_Value(tmp11)),
          m_ZExt(
            m_Value(tmp12)))),
      m_c_Mul(
        m_ZExt(
          m_Value(tmp13)),
        m_ZExt(
          m_Value(tmp14))))) &&
hasBitWidth(tmp0, 8) &&
hasBitWidth(tmp1, 8) &&
hasBitWidth(tmp2, 32) &&
hasBitWidth(tmp3, 8) &&
hasBitWidth(tmp4, 8) &&
hasBitWidth(tmp5, 8) &&
hasBitWidth(tmp6, 8) &&
hasBitWidth(tmp7, 8) &&
hasBitWidth(tmp8, 8) &&
hasBitWidth(tmp9, 8) &&
hasBitWidth(tmp10, 8) &&
hasBitWidth(tmp11, 8) &&
hasBitWidth(tmp12, 8) &&
hasBitWidth(tmp13, 8) &&
hasBitWidth(tmp14, 8);
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation154;
  

class : public Operation {
  bool match(
    Value *V, std::vector<Match> &Matches) const override {
    
    Value *tmp0; Value *tmp1; Value *tmp2; Value *tmp3; Value *tmp4; Value *tmp5; Value *tmp6; Value *tmp7; Value *tmp8; Value *tmp9; Value *tmp10; Value *tmp11; Value *tmp12; Value *tmp13; Value *tmp14;
    bool Matched = hasBitWidth(V, 32) &&
PatternMatch::match(V, m_c_Add(
      m_c_Add(
        m_c_Add(
          m_c_Add(
            m_c_Add(
              m_c_Add(
                m_c_Add(
                  m_c_Mul(
                    m_SExt(
                      m_Value(tmp0)),
                    m_ZExt(
                      m_Value(tmp1))),
                  m_Value(tmp2)),
                m_c_Mul(
                  m_SExt(
                    m_Value(tmp3)),
                  m_ZExt(
                    m_Value(tmp4)))),
              m_c_Mul(
                m_SExt(
                  m_Value(tmp5)),
                m_ZExt(
                  m_Value(tmp6)))),
            m_c_Mul(
              m_SExt(
                m_Value(tmp7)),
              m_ZExt(
                m_Value(tmp8)))),
          m_c_Mul(
            m_SExt(
              m_Value(tmp9)),
            m_ZExt(
              m_Value(tmp10)))),
        m_c_Mul(
          m_SExt(
            m_Value(tmp11)),
          m_ZExt(
            m_Value(tmp12)))),
      m_c_Mul(
        m_SExt(
          m_Value(tmp13)),
        m_ZExt(
          m_Value(tmp14))))) &&
hasBitWidth(tmp0, 8) &&
hasBitWidth(tmp1, 8) &&
hasBitWidth(tmp2, 32) &&
hasBitWidth(tmp3, 8) &&
hasBitWidth(tmp4, 8) &&
hasBitWidth(tmp5, 8) &&
hasBitWidth(tmp6, 8) &&
hasBitWidth(tmp7, 8) &&
hasBitWidth(tmp8, 8) &&
hasBitWidth(tmp9, 8) &&
hasBitWidth(tmp10, 8) &&
hasBitWidth(tmp11, 8) &&
hasBitWidth(tmp12, 8) &&
hasBitWidth(tmp13, 8) &&
hasBitWidth(tmp14, 8);
    if (Matched)
      Matches.push_back({
      false,
      // matched live ins
      { tmp0, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8, tmp9, tmp10, tmp11, tmp12, tmp13, tmp14 },
      // the matched value itself
      V
      });
    return Matched;
    
  }
} Operation155;
  
std::vector<InstBinding> ArmInsts {
  InstBinding("vaddl_s8", {  }, InstSignature { { 64, 64 }, { 128 }, false }, { BoundOperation(&Operation0, { InputSlice { 1, 0, 8 }, InputSlice { 0, 0, 8 } }), BoundOperation(&Operation0, { InputSlice { 1, 8, 16 }, InputSlice { 0, 8, 16 } }), BoundOperation(&Operation0, { InputSlice { 1, 16, 24 }, InputSlice { 0, 16, 24 } }), BoundOperation(&Operation0, { InputSlice { 1, 24, 32 }, InputSlice { 0, 24, 32 } }), BoundOperation(&Operation0, { InputSlice { 1, 32, 40 }, InputSlice { 0, 32, 40 } }), BoundOperation(&Operation0, { InputSlice { 1, 40, 48 }, InputSlice { 0, 40, 48 } }), BoundOperation(&Operation0, { InputSlice { 1, 48, 56 }, InputSlice { 0, 48, 56 } }), BoundOperation(&Operation0, { InputSlice { 1, 56, 64 }, InputSlice { 0, 56, 64 } }) }, 1),
InstBinding("vaddl_s16", {  }, InstSignature { { 64, 64 }, { 128 }, false }, { BoundOperation(&Operation1, { InputSlice { 1, 0, 16 }, InputSlice { 0, 0, 16 } }), BoundOperation(&Operation1, { InputSlice { 1, 16, 32 }, InputSlice { 0, 16, 32 } }), BoundOperation(&Operation1, { InputSlice { 1, 32, 48 }, InputSlice { 0, 32, 48 } }), BoundOperation(&Operation1, { InputSlice { 1, 48, 64 }, InputSlice { 0, 48, 64 } }) }, 1),
InstBinding("vaddl_s32", {  }, InstSignature { { 64, 64 }, { 128 }, false }, { BoundOperation(&Operation2, { InputSlice { 1, 0, 32 }, InputSlice { 0, 0, 32 } }), BoundOperation(&Operation2, { InputSlice { 1, 32, 64 }, InputSlice { 0, 32, 64 } }) }, 1),
InstBinding("vaddl_u8", {  }, InstSignature { { 64, 64 }, { 128 }, false }, { BoundOperation(&Operation3, { InputSlice { 1, 0, 8 }, InputSlice { 0, 0, 8 } }), BoundOperation(&Operation3, { InputSlice { 1, 8, 16 }, InputSlice { 0, 8, 16 } }), BoundOperation(&Operation3, { InputSlice { 1, 16, 24 }, InputSlice { 0, 16, 24 } }), BoundOperation(&Operation3, { InputSlice { 1, 24, 32 }, InputSlice { 0, 24, 32 } }), BoundOperation(&Operation3, { InputSlice { 1, 32, 40 }, InputSlice { 0, 32, 40 } }), BoundOperation(&Operation3, { InputSlice { 1, 40, 48 }, InputSlice { 0, 40, 48 } }), BoundOperation(&Operation3, { InputSlice { 1, 48, 56 }, InputSlice { 0, 48, 56 } }), BoundOperation(&Operation3, { InputSlice { 1, 56, 64 }, InputSlice { 0, 56, 64 } }) }, 1),
InstBinding("vaddl_u16", {  }, InstSignature { { 64, 64 }, { 128 }, false }, { BoundOperation(&Operation4, { InputSlice { 1, 0, 16 }, InputSlice { 0, 0, 16 } }), BoundOperation(&Operation4, { InputSlice { 1, 16, 32 }, InputSlice { 0, 16, 32 } }), BoundOperation(&Operation4, { InputSlice { 1, 32, 48 }, InputSlice { 0, 32, 48 } }), BoundOperation(&Operation4, { InputSlice { 1, 48, 64 }, InputSlice { 0, 48, 64 } }) }, 1),
InstBinding("vaddl_u32", {  }, InstSignature { { 64, 64 }, { 128 }, false }, { BoundOperation(&Operation5, { InputSlice { 1, 0, 32 }, InputSlice { 0, 0, 32 } }), BoundOperation(&Operation5, { InputSlice { 1, 32, 64 }, InputSlice { 0, 32, 64 } }) }, 1),
InstBinding("vaddw_s8", {  }, InstSignature { { 128, 64 }, { 128 }, false }, { BoundOperation(&Operation6, { InputSlice { 1, 0, 8 }, InputSlice { 0, 0, 16 } }), BoundOperation(&Operation6, { InputSlice { 1, 8, 16 }, InputSlice { 0, 16, 32 } }), BoundOperation(&Operation6, { InputSlice { 1, 16, 24 }, InputSlice { 0, 32, 48 } }), BoundOperation(&Operation6, { InputSlice { 1, 24, 32 }, InputSlice { 0, 48, 64 } }), BoundOperation(&Operation6, { InputSlice { 1, 32, 40 }, InputSlice { 0, 64, 80 } }), BoundOperation(&Operation6, { InputSlice { 1, 40, 48 }, InputSlice { 0, 80, 96 } }), BoundOperation(&Operation6, { InputSlice { 1, 48, 56 }, InputSlice { 0, 96, 112 } }), BoundOperation(&Operation6, { InputSlice { 1, 56, 64 }, InputSlice { 0, 112, 128 } }) }, 1),
InstBinding("vaddw_s16", {  }, InstSignature { { 128, 64 }, { 128 }, false }, { BoundOperation(&Operation7, { InputSlice { 1, 0, 16 }, InputSlice { 0, 0, 32 } }), BoundOperation(&Operation7, { InputSlice { 1, 16, 32 }, InputSlice { 0, 32, 64 } }), BoundOperation(&Operation7, { InputSlice { 1, 32, 48 }, InputSlice { 0, 64, 96 } }), BoundOperation(&Operation7, { InputSlice { 1, 48, 64 }, InputSlice { 0, 96, 128 } }) }, 1),
InstBinding("vaddw_s32", {  }, InstSignature { { 128, 64 }, { 128 }, false }, { BoundOperation(&Operation8, { InputSlice { 1, 0, 32 }, InputSlice { 0, 0, 64 } }), BoundOperation(&Operation8, { InputSlice { 1, 32, 64 }, InputSlice { 0, 64, 128 } }) }, 1),
InstBinding("vaddw_u8", {  }, InstSignature { { 128, 64 }, { 128 }, false }, { BoundOperation(&Operation9, { InputSlice { 1, 0, 8 }, InputSlice { 0, 0, 16 } }), BoundOperation(&Operation9, { InputSlice { 1, 8, 16 }, InputSlice { 0, 16, 32 } }), BoundOperation(&Operation9, { InputSlice { 1, 16, 24 }, InputSlice { 0, 32, 48 } }), BoundOperation(&Operation9, { InputSlice { 1, 24, 32 }, InputSlice { 0, 48, 64 } }), BoundOperation(&Operation9, { InputSlice { 1, 32, 40 }, InputSlice { 0, 64, 80 } }), BoundOperation(&Operation9, { InputSlice { 1, 40, 48 }, InputSlice { 0, 80, 96 } }), BoundOperation(&Operation9, { InputSlice { 1, 48, 56 }, InputSlice { 0, 96, 112 } }), BoundOperation(&Operation9, { InputSlice { 1, 56, 64 }, InputSlice { 0, 112, 128 } }) }, 1),
InstBinding("vaddw_u16", {  }, InstSignature { { 128, 64 }, { 128 }, false }, { BoundOperation(&Operation10, { InputSlice { 1, 0, 16 }, InputSlice { 0, 0, 32 } }), BoundOperation(&Operation10, { InputSlice { 1, 16, 32 }, InputSlice { 0, 32, 64 } }), BoundOperation(&Operation10, { InputSlice { 1, 32, 48 }, InputSlice { 0, 64, 96 } }), BoundOperation(&Operation10, { InputSlice { 1, 48, 64 }, InputSlice { 0, 96, 128 } }) }, 1),
InstBinding("vaddw_u32", {  }, InstSignature { { 128, 64 }, { 128 }, false }, { BoundOperation(&Operation11, { InputSlice { 1, 0, 32 }, InputSlice { 0, 0, 64 } }), BoundOperation(&Operation11, { InputSlice { 1, 32, 64 }, InputSlice { 0, 64, 128 } }) }, 1),
InstBinding("vhadd_s8", {  }, InstSignature { { 64, 64 }, { 64 }, false }, { BoundOperation(&Operation12, { InputSlice { 1, 0, 8 }, InputSlice { 0, 0, 8 } }), BoundOperation(&Operation12, { InputSlice { 1, 8, 16 }, InputSlice { 0, 8, 16 } }), BoundOperation(&Operation12, { InputSlice { 1, 16, 24 }, InputSlice { 0, 16, 24 } }), BoundOperation(&Operation12, { InputSlice { 1, 24, 32 }, InputSlice { 0, 24, 32 } }), BoundOperation(&Operation12, { InputSlice { 1, 32, 40 }, InputSlice { 0, 32, 40 } }), BoundOperation(&Operation12, { InputSlice { 1, 40, 48 }, InputSlice { 0, 40, 48 } }), BoundOperation(&Operation12, { InputSlice { 1, 48, 56 }, InputSlice { 0, 48, 56 } }), BoundOperation(&Operation12, { InputSlice { 1, 56, 64 }, InputSlice { 0, 56, 64 } }) }, 1),
InstBinding("vhadd_s16", {  }, InstSignature { { 64, 64 }, { 64 }, false }, { BoundOperation(&Operation13, { InputSlice { 1, 0, 16 }, InputSlice { 0, 0, 16 } }), BoundOperation(&Operation13, { InputSlice { 1, 16, 32 }, InputSlice { 0, 16, 32 } }), BoundOperation(&Operation13, { InputSlice { 1, 32, 48 }, InputSlice { 0, 32, 48 } }), BoundOperation(&Operation13, { InputSlice { 1, 48, 64 }, InputSlice { 0, 48, 64 } }) }, 1),
InstBinding("vhadd_s32", {  }, InstSignature { { 64, 64 }, { 64 }, false }, { BoundOperation(&Operation14, { InputSlice { 1, 0, 32 }, InputSlice { 0, 0, 32 } }), BoundOperation(&Operation14, { InputSlice { 1, 32, 64 }, InputSlice { 0, 32, 64 } }) }, 1),
InstBinding("vhadd_u8", {  }, InstSignature { { 64, 64 }, { 64 }, false }, { BoundOperation(&Operation15, { InputSlice { 1, 0, 8 }, InputSlice { 0, 0, 8 } }), BoundOperation(&Operation15, { InputSlice { 1, 8, 16 }, InputSlice { 0, 8, 16 } }), BoundOperation(&Operation15, { InputSlice { 1, 16, 24 }, InputSlice { 0, 16, 24 } }), BoundOperation(&Operation15, { InputSlice { 1, 24, 32 }, InputSlice { 0, 24, 32 } }), BoundOperation(&Operation15, { InputSlice { 1, 32, 40 }, InputSlice { 0, 32, 40 } }), BoundOperation(&Operation15, { InputSlice { 1, 40, 48 }, InputSlice { 0, 40, 48 } }), BoundOperation(&Operation15, { InputSlice { 1, 48, 56 }, InputSlice { 0, 48, 56 } }), BoundOperation(&Operation15, { InputSlice { 1, 56, 64 }, InputSlice { 0, 56, 64 } }) }, 1),
InstBinding("vhadd_u16", {  }, InstSignature { { 64, 64 }, { 64 }, false }, { BoundOperation(&Operation16, { InputSlice { 1, 0, 16 }, InputSlice { 0, 0, 16 } }), BoundOperation(&Operation16, { InputSlice { 1, 16, 32 }, InputSlice { 0, 16, 32 } }), BoundOperation(&Operation16, { InputSlice { 1, 32, 48 }, InputSlice { 0, 32, 48 } }), BoundOperation(&Operation16, { InputSlice { 1, 48, 64 }, InputSlice { 0, 48, 64 } }) }, 1),
InstBinding("vhadd_u32", {  }, InstSignature { { 64, 64 }, { 64 }, false }, { BoundOperation(&Operation17, { InputSlice { 1, 0, 32 }, InputSlice { 0, 0, 32 } }), BoundOperation(&Operation17, { InputSlice { 1, 32, 64 }, InputSlice { 0, 32, 64 } }) }, 1),
InstBinding("vhaddq_s8", {  }, InstSignature { { 128, 128 }, { 128 }, false }, { BoundOperation(&Operation12, { InputSlice { 1, 0, 8 }, InputSlice { 0, 0, 8 } }), BoundOperation(&Operation12, { InputSlice { 1, 8, 16 }, InputSlice { 0, 8, 16 } }), BoundOperation(&Operation12, { InputSlice { 1, 16, 24 }, InputSlice { 0, 16, 24 } }), BoundOperation(&Operation12, { InputSlice { 1, 24, 32 }, InputSlice { 0, 24, 32 } }), BoundOperation(&Operation12, { InputSlice { 1, 32, 40 }, InputSlice { 0, 32, 40 } }), BoundOperation(&Operation12, { InputSlice { 1, 40, 48 }, InputSlice { 0, 40, 48 } }), BoundOperation(&Operation12, { InputSlice { 1, 48, 56 }, InputSlice { 0, 48, 56 } }), BoundOperation(&Operation12, { InputSlice { 1, 56, 64 }, InputSlice { 0, 56, 64 } }), BoundOperation(&Operation12, { InputSlice { 1, 64, 72 }, InputSlice { 0, 64, 72 } }), BoundOperation(&Operation12, { InputSlice { 1, 72, 80 }, InputSlice { 0, 72, 80 } }), BoundOperation(&Operation12, { InputSlice { 1, 80, 88 }, InputSlice { 0, 80, 88 } }), BoundOperation(&Operation12, { InputSlice { 1, 88, 96 }, InputSlice { 0, 88, 96 } }), BoundOperation(&Operation12, { InputSlice { 1, 96, 104 }, InputSlice { 0, 96, 104 } }), BoundOperation(&Operation12, { InputSlice { 1, 104, 112 }, InputSlice { 0, 104, 112 } }), BoundOperation(&Operation12, { InputSlice { 1, 112, 120 }, InputSlice { 0, 112, 120 } }), BoundOperation(&Operation12, { InputSlice { 1, 120, 128 }, InputSlice { 0, 120, 128 } }) }, 1),
InstBinding("vhaddq_s16", {  }, InstSignature { { 128, 128 }, { 128 }, false }, { BoundOperation(&Operation13, { InputSlice { 1, 0, 16 }, InputSlice { 0, 0, 16 } }), BoundOperation(&Operation13, { InputSlice { 1, 16, 32 }, InputSlice { 0, 16, 32 } }), BoundOperation(&Operation13, { InputSlice { 1, 32, 48 }, InputSlice { 0, 32, 48 } }), BoundOperation(&Operation13, { InputSlice { 1, 48, 64 }, InputSlice { 0, 48, 64 } }), BoundOperation(&Operation13, { InputSlice { 1, 64, 80 }, InputSlice { 0, 64, 80 } }), BoundOperation(&Operation13, { InputSlice { 1, 80, 96 }, InputSlice { 0, 80, 96 } }), BoundOperation(&Operation13, { InputSlice { 1, 96, 112 }, InputSlice { 0, 96, 112 } }), BoundOperation(&Operation13, { InputSlice { 1, 112, 128 }, InputSlice { 0, 112, 128 } }) }, 1),
InstBinding("vhaddq_s32", {  }, InstSignature { { 128, 128 }, { 128 }, false }, { BoundOperation(&Operation14, { InputSlice { 1, 0, 32 }, InputSlice { 0, 0, 32 } }), BoundOperation(&Operation14, { InputSlice { 1, 32, 64 }, InputSlice { 0, 32, 64 } }), BoundOperation(&Operation14, { InputSlice { 1, 64, 96 }, InputSlice { 0, 64, 96 } }), BoundOperation(&Operation14, { InputSlice { 1, 96, 128 }, InputSlice { 0, 96, 128 } }) }, 1),
InstBinding("vhaddq_u8", {  }, InstSignature { { 128, 128 }, { 128 }, false }, { BoundOperation(&Operation15, { InputSlice { 1, 0, 8 }, InputSlice { 0, 0, 8 } }), BoundOperation(&Operation15, { InputSlice { 1, 8, 16 }, InputSlice { 0, 8, 16 } }), BoundOperation(&Operation15, { InputSlice { 1, 16, 24 }, InputSlice { 0, 16, 24 } }), BoundOperation(&Operation15, { InputSlice { 1, 24, 32 }, InputSlice { 0, 24, 32 } }), BoundOperation(&Operation15, { InputSlice { 1, 32, 40 }, InputSlice { 0, 32, 40 } }), BoundOperation(&Operation15, { InputSlice { 1, 40, 48 }, InputSlice { 0, 40, 48 } }), BoundOperation(&Operation15, { InputSlice { 1, 48, 56 }, InputSlice { 0, 48, 56 } }), BoundOperation(&Operation15, { InputSlice { 1, 56, 64 }, InputSlice { 0, 56, 64 } }), BoundOperation(&Operation15, { InputSlice { 1, 64, 72 }, InputSlice { 0, 64, 72 } }), BoundOperation(&Operation15, { InputSlice { 1, 72, 80 }, InputSlice { 0, 72, 80 } }), BoundOperation(&Operation15, { InputSlice { 1, 80, 88 }, InputSlice { 0, 80, 88 } }), BoundOperation(&Operation15, { InputSlice { 1, 88, 96 }, InputSlice { 0, 88, 96 } }), BoundOperation(&Operation15, { InputSlice { 1, 96, 104 }, InputSlice { 0, 96, 104 } }), BoundOperation(&Operation15, { InputSlice { 1, 104, 112 }, InputSlice { 0, 104, 112 } }), BoundOperation(&Operation15, { InputSlice { 1, 112, 120 }, InputSlice { 0, 112, 120 } }), BoundOperation(&Operation15, { InputSlice { 1, 120, 128 }, InputSlice { 0, 120, 128 } }) }, 1),
InstBinding("vhaddq_u16", {  }, InstSignature { { 128, 128 }, { 128 }, false }, { BoundOperation(&Operation16, { InputSlice { 1, 0, 16 }, InputSlice { 0, 0, 16 } }), BoundOperation(&Operation16, { InputSlice { 1, 16, 32 }, InputSlice { 0, 16, 32 } }), BoundOperation(&Operation16, { InputSlice { 1, 32, 48 }, InputSlice { 0, 32, 48 } }), BoundOperation(&Operation16, { InputSlice { 1, 48, 64 }, InputSlice { 0, 48, 64 } }), BoundOperation(&Operation16, { InputSlice { 1, 64, 80 }, InputSlice { 0, 64, 80 } }), BoundOperation(&Operation16, { InputSlice { 1, 80, 96 }, InputSlice { 0, 80, 96 } }), BoundOperation(&Operation16, { InputSlice { 1, 96, 112 }, InputSlice { 0, 96, 112 } }), BoundOperation(&Operation16, { InputSlice { 1, 112, 128 }, InputSlice { 0, 112, 128 } }) }, 1),
InstBinding("vhaddq_u32", {  }, InstSignature { { 128, 128 }, { 128 }, false }, { BoundOperation(&Operation17, { InputSlice { 1, 0, 32 }, InputSlice { 0, 0, 32 } }), BoundOperation(&Operation17, { InputSlice { 1, 32, 64 }, InputSlice { 0, 32, 64 } }), BoundOperation(&Operation17, { InputSlice { 1, 64, 96 }, InputSlice { 0, 64, 96 } }), BoundOperation(&Operation17, { InputSlice { 1, 96, 128 }, InputSlice { 0, 96, 128 } }) }, 1),
InstBinding("vrhadd_s8", {  }, InstSignature { { 64, 64 }, { 64 }, false }, { BoundOperation(&Operation18, { InputSlice { 0, 0, 8 }, InputSlice { 1, 0, 8 } }), BoundOperation(&Operation18, { InputSlice { 0, 8, 16 }, InputSlice { 1, 8, 16 } }), BoundOperation(&Operation18, { InputSlice { 0, 16, 24 }, InputSlice { 1, 16, 24 } }), BoundOperation(&Operation18, { InputSlice { 0, 24, 32 }, InputSlice { 1, 24, 32 } }), BoundOperation(&Operation18, { InputSlice { 0, 32, 40 }, InputSlice { 1, 32, 40 } }), BoundOperation(&Operation18, { InputSlice { 0, 40, 48 }, InputSlice { 1, 40, 48 } }), BoundOperation(&Operation18, { InputSlice { 0, 48, 56 }, InputSlice { 1, 48, 56 } }), BoundOperation(&Operation18, { InputSlice { 0, 56, 64 }, InputSlice { 1, 56, 64 } }) }, 1),
InstBinding("vrhadd_s16", {  }, InstSignature { { 64, 64 }, { 64 }, false }, { BoundOperation(&Operation19, { InputSlice { 0, 0, 16 }, InputSlice { 1, 0, 16 } }), BoundOperation(&Operation19, { InputSlice { 0, 16, 32 }, InputSlice { 1, 16, 32 } }), BoundOperation(&Operation19, { InputSlice { 0, 32, 48 }, InputSlice { 1, 32, 48 } }), BoundOperation(&Operation19, { InputSlice { 0, 48, 64 }, InputSlice { 1, 48, 64 } }) }, 1),
InstBinding("vrhadd_s32", {  }, InstSignature { { 64, 64 }, { 64 }, false }, { BoundOperation(&Operation20, { InputSlice { 0, 0, 32 }, InputSlice { 1, 0, 32 } }), BoundOperation(&Operation20, { InputSlice { 0, 32, 64 }, InputSlice { 1, 32, 64 } }) }, 1),
InstBinding("vrhadd_u8", {  }, InstSignature { { 64, 64 }, { 64 }, false }, { BoundOperation(&Operation21, { InputSlice { 0, 0, 8 }, InputSlice { 1, 0, 8 } }), BoundOperation(&Operation21, { InputSlice { 0, 8, 16 }, InputSlice { 1, 8, 16 } }), BoundOperation(&Operation21, { InputSlice { 0, 16, 24 }, InputSlice { 1, 16, 24 } }), BoundOperation(&Operation21, { InputSlice { 0, 24, 32 }, InputSlice { 1, 24, 32 } }), BoundOperation(&Operation21, { InputSlice { 0, 32, 40 }, InputSlice { 1, 32, 40 } }), BoundOperation(&Operation21, { InputSlice { 0, 40, 48 }, InputSlice { 1, 40, 48 } }), BoundOperation(&Operation21, { InputSlice { 0, 48, 56 }, InputSlice { 1, 48, 56 } }), BoundOperation(&Operation21, { InputSlice { 0, 56, 64 }, InputSlice { 1, 56, 64 } }) }, 1),
InstBinding("vrhadd_u16", {  }, InstSignature { { 64, 64 }, { 64 }, false }, { BoundOperation(&Operation22, { InputSlice { 0, 0, 16 }, InputSlice { 1, 0, 16 } }), BoundOperation(&Operation22, { InputSlice { 0, 16, 32 }, InputSlice { 1, 16, 32 } }), BoundOperation(&Operation22, { InputSlice { 0, 32, 48 }, InputSlice { 1, 32, 48 } }), BoundOperation(&Operation22, { InputSlice { 0, 48, 64 }, InputSlice { 1, 48, 64 } }) }, 1),
InstBinding("vrhadd_u32", {  }, InstSignature { { 64, 64 }, { 64 }, false }, { BoundOperation(&Operation23, { InputSlice { 0, 0, 32 }, InputSlice { 1, 0, 32 } }), BoundOperation(&Operation23, { InputSlice { 0, 32, 64 }, InputSlice { 1, 32, 64 } }) }, 1),
InstBinding("vrhaddq_s8", {  }, InstSignature { { 128, 128 }, { 128 }, false }, { BoundOperation(&Operation18, { InputSlice { 0, 0, 8 }, InputSlice { 1, 0, 8 } }), BoundOperation(&Operation18, { InputSlice { 0, 8, 16 }, InputSlice { 1, 8, 16 } }), BoundOperation(&Operation18, { InputSlice { 0, 16, 24 }, InputSlice { 1, 16, 24 } }), BoundOperation(&Operation18, { InputSlice { 0, 24, 32 }, InputSlice { 1, 24, 32 } }), BoundOperation(&Operation18, { InputSlice { 0, 32, 40 }, InputSlice { 1, 32, 40 } }), BoundOperation(&Operation18, { InputSlice { 0, 40, 48 }, InputSlice { 1, 40, 48 } }), BoundOperation(&Operation18, { InputSlice { 0, 48, 56 }, InputSlice { 1, 48, 56 } }), BoundOperation(&Operation18, { InputSlice { 0, 56, 64 }, InputSlice { 1, 56, 64 } }), BoundOperation(&Operation18, { InputSlice { 0, 64, 72 }, InputSlice { 1, 64, 72 } }), BoundOperation(&Operation18, { InputSlice { 0, 72, 80 }, InputSlice { 1, 72, 80 } }), BoundOperation(&Operation18, { InputSlice { 0, 80, 88 }, InputSlice { 1, 80, 88 } }), BoundOperation(&Operation18, { InputSlice { 0, 88, 96 }, InputSlice { 1, 88, 96 } }), BoundOperation(&Operation18, { InputSlice { 0, 96, 104 }, InputSlice { 1, 96, 104 } }), BoundOperation(&Operation18, { InputSlice { 0, 104, 112 }, InputSlice { 1, 104, 112 } }), BoundOperation(&Operation18, { InputSlice { 0, 112, 120 }, InputSlice { 1, 112, 120 } }), BoundOperation(&Operation18, { InputSlice { 0, 120, 128 }, InputSlice { 1, 120, 128 } }) }, 1),
InstBinding("vrhaddq_s16", {  }, InstSignature { { 128, 128 }, { 128 }, false }, { BoundOperation(&Operation19, { InputSlice { 0, 0, 16 }, InputSlice { 1, 0, 16 } }), BoundOperation(&Operation19, { InputSlice { 0, 16, 32 }, InputSlice { 1, 16, 32 } }), BoundOperation(&Operation19, { InputSlice { 0, 32, 48 }, InputSlice { 1, 32, 48 } }), BoundOperation(&Operation19, { InputSlice { 0, 48, 64 }, InputSlice { 1, 48, 64 } }), BoundOperation(&Operation19, { InputSlice { 0, 64, 80 }, InputSlice { 1, 64, 80 } }), BoundOperation(&Operation19, { InputSlice { 0, 80, 96 }, InputSlice { 1, 80, 96 } }), BoundOperation(&Operation19, { InputSlice { 0, 96, 112 }, InputSlice { 1, 96, 112 } }), BoundOperation(&Operation19, { InputSlice { 0, 112, 128 }, InputSlice { 1, 112, 128 } }) }, 1),
InstBinding("vrhaddq_s32", {  }, InstSignature { { 128, 128 }, { 128 }, false }, { BoundOperation(&Operation20, { InputSlice { 0, 0, 32 }, InputSlice { 1, 0, 32 } }), BoundOperation(&Operation20, { InputSlice { 0, 32, 64 }, InputSlice { 1, 32, 64 } }), BoundOperation(&Operation20, { InputSlice { 0, 64, 96 }, InputSlice { 1, 64, 96 } }), BoundOperation(&Operation20, { InputSlice { 0, 96, 128 }, InputSlice { 1, 96, 128 } }) }, 1),
InstBinding("vrhaddq_u8", {  }, InstSignature { { 128, 128 }, { 128 }, false }, { BoundOperation(&Operation21, { InputSlice { 0, 0, 8 }, InputSlice { 1, 0, 8 } }), BoundOperation(&Operation21, { InputSlice { 0, 8, 16 }, InputSlice { 1, 8, 16 } }), BoundOperation(&Operation21, { InputSlice { 0, 16, 24 }, InputSlice { 1, 16, 24 } }), BoundOperation(&Operation21, { InputSlice { 0, 24, 32 }, InputSlice { 1, 24, 32 } }), BoundOperation(&Operation21, { InputSlice { 0, 32, 40 }, InputSlice { 1, 32, 40 } }), BoundOperation(&Operation21, { InputSlice { 0, 40, 48 }, InputSlice { 1, 40, 48 } }), BoundOperation(&Operation21, { InputSlice { 0, 48, 56 }, InputSlice { 1, 48, 56 } }), BoundOperation(&Operation21, { InputSlice { 0, 56, 64 }, InputSlice { 1, 56, 64 } }), BoundOperation(&Operation21, { InputSlice { 0, 64, 72 }, InputSlice { 1, 64, 72 } }), BoundOperation(&Operation21, { InputSlice { 0, 72, 80 }, InputSlice { 1, 72, 80 } }), BoundOperation(&Operation21, { InputSlice { 0, 80, 88 }, InputSlice { 1, 80, 88 } }), BoundOperation(&Operation21, { InputSlice { 0, 88, 96 }, InputSlice { 1, 88, 96 } }), BoundOperation(&Operation21, { InputSlice { 0, 96, 104 }, InputSlice { 1, 96, 104 } }), BoundOperation(&Operation21, { InputSlice { 0, 104, 112 }, InputSlice { 1, 104, 112 } }), BoundOperation(&Operation21, { InputSlice { 0, 112, 120 }, InputSlice { 1, 112, 120 } }), BoundOperation(&Operation21, { InputSlice { 0, 120, 128 }, InputSlice { 1, 120, 128 } }) }, 1),
InstBinding("vrhaddq_u16", {  }, InstSignature { { 128, 128 }, { 128 }, false }, { BoundOperation(&Operation22, { InputSlice { 0, 0, 16 }, InputSlice { 1, 0, 16 } }), BoundOperation(&Operation22, { InputSlice { 0, 16, 32 }, InputSlice { 1, 16, 32 } }), BoundOperation(&Operation22, { InputSlice { 0, 32, 48 }, InputSlice { 1, 32, 48 } }), BoundOperation(&Operation22, { InputSlice { 0, 48, 64 }, InputSlice { 1, 48, 64 } }), BoundOperation(&Operation22, { InputSlice { 0, 64, 80 }, InputSlice { 1, 64, 80 } }), BoundOperation(&Operation22, { InputSlice { 0, 80, 96 }, InputSlice { 1, 80, 96 } }), BoundOperation(&Operation22, { InputSlice { 0, 96, 112 }, InputSlice { 1, 96, 112 } }), BoundOperation(&Operation22, { InputSlice { 0, 112, 128 }, InputSlice { 1, 112, 128 } }) }, 1),
InstBinding("vrhaddq_u32", {  }, InstSignature { { 128, 128 }, { 128 }, false }, { BoundOperation(&Operation23, { InputSlice { 0, 0, 32 }, InputSlice { 1, 0, 32 } }), BoundOperation(&Operation23, { InputSlice { 0, 32, 64 }, InputSlice { 1, 32, 64 } }), BoundOperation(&Operation23, { InputSlice { 0, 64, 96 }, InputSlice { 1, 64, 96 } }), BoundOperation(&Operation23, { InputSlice { 0, 96, 128 }, InputSlice { 1, 96, 128 } }) }, 1),
InstBinding("vqadd_s8", {  }, InstSignature { { 64, 64 }, { 64 }, false }, { BoundOperation(&Operation24, { InputSlice { 0, 0, 8 }, InputSlice { 1, 0, 8 } }), BoundOperation(&Operation24, { InputSlice { 0, 8, 16 }, InputSlice { 1, 8, 16 } }), BoundOperation(&Operation24, { InputSlice { 0, 16, 24 }, InputSlice { 1, 16, 24 } }), BoundOperation(&Operation24, { InputSlice { 0, 24, 32 }, InputSlice { 1, 24, 32 } }), BoundOperation(&Operation24, { InputSlice { 0, 32, 40 }, InputSlice { 1, 32, 40 } }), BoundOperation(&Operation24, { InputSlice { 0, 40, 48 }, InputSlice { 1, 40, 48 } }), BoundOperation(&Operation24, { InputSlice { 0, 48, 56 }, InputSlice { 1, 48, 56 } }), BoundOperation(&Operation24, { InputSlice { 0, 56, 64 }, InputSlice { 1, 56, 64 } }) }, 1),
InstBinding("vqadd_s16", {  }, InstSignature { { 64, 64 }, { 64 }, false }, { BoundOperation(&Operation25, { InputSlice { 0, 0, 16 }, InputSlice { 1, 0, 16 } }), BoundOperation(&Operation25, { InputSlice { 0, 16, 32 }, InputSlice { 1, 16, 32 } }), BoundOperation(&Operation25, { InputSlice { 0, 32, 48 }, InputSlice { 1, 32, 48 } }), BoundOperation(&Operation25, { InputSlice { 0, 48, 64 }, InputSlice { 1, 48, 64 } }) }, 1),
InstBinding("vqadd_s32", {  }, InstSignature { { 64, 64 }, { 64 }, false }, { BoundOperation(&Operation26, { InputSlice { 0, 0, 32 }, InputSlice { 1, 0, 32 } }), BoundOperation(&Operation26, { InputSlice { 0, 32, 64 }, InputSlice { 1, 32, 64 } }) }, 1),
InstBinding("vqadd_u8", {  }, InstSignature { { 64, 64 }, { 64 }, false }, { BoundOperation(&Operation27, { InputSlice { 1, 0, 8 }, InputSlice { 0, 0, 8 } }), BoundOperation(&Operation27, { InputSlice { 1, 8, 16 }, InputSlice { 0, 8, 16 } }), BoundOperation(&Operation27, { InputSlice { 1, 16, 24 }, InputSlice { 0, 16, 24 } }), BoundOperation(&Operation27, { InputSlice { 1, 24, 32 }, InputSlice { 0, 24, 32 } }), BoundOperation(&Operation27, { InputSlice { 1, 32, 40 }, InputSlice { 0, 32, 40 } }), BoundOperation(&Operation27, { InputSlice { 1, 40, 48 }, InputSlice { 0, 40, 48 } }), BoundOperation(&Operation27, { InputSlice { 1, 48, 56 }, InputSlice { 0, 48, 56 } }), BoundOperation(&Operation27, { InputSlice { 1, 56, 64 }, InputSlice { 0, 56, 64 } }) }, 1),
InstBinding("vqadd_u16", {  }, InstSignature { { 64, 64 }, { 64 }, false }, { BoundOperation(&Operation28, { InputSlice { 1, 0, 16 }, InputSlice { 0, 0, 16 } }), BoundOperation(&Operation28, { InputSlice { 1, 16, 32 }, InputSlice { 0, 16, 32 } }), BoundOperation(&Operation28, { InputSlice { 1, 32, 48 }, InputSlice { 0, 32, 48 } }), BoundOperation(&Operation28, { InputSlice { 1, 48, 64 }, InputSlice { 0, 48, 64 } }) }, 1),
InstBinding("vqadd_u32", {  }, InstSignature { { 64, 64 }, { 64 }, false }, { BoundOperation(&Operation29, { InputSlice { 1, 0, 32 }, InputSlice { 0, 0, 32 } }), BoundOperation(&Operation29, { InputSlice { 1, 32, 64 }, InputSlice { 0, 32, 64 } }) }, 1),
InstBinding("vqaddq_s8", {  }, InstSignature { { 128, 128 }, { 128 }, false }, { BoundOperation(&Operation24, { InputSlice { 0, 0, 8 }, InputSlice { 1, 0, 8 } }), BoundOperation(&Operation24, { InputSlice { 0, 8, 16 }, InputSlice { 1, 8, 16 } }), BoundOperation(&Operation24, { InputSlice { 0, 16, 24 }, InputSlice { 1, 16, 24 } }), BoundOperation(&Operation24, { InputSlice { 0, 24, 32 }, InputSlice { 1, 24, 32 } }), BoundOperation(&Operation24, { InputSlice { 0, 32, 40 }, InputSlice { 1, 32, 40 } }), BoundOperation(&Operation24, { InputSlice { 0, 40, 48 }, InputSlice { 1, 40, 48 } }), BoundOperation(&Operation24, { InputSlice { 0, 48, 56 }, InputSlice { 1, 48, 56 } }), BoundOperation(&Operation24, { InputSlice { 0, 56, 64 }, InputSlice { 1, 56, 64 } }), BoundOperation(&Operation24, { InputSlice { 0, 64, 72 }, InputSlice { 1, 64, 72 } }), BoundOperation(&Operation24, { InputSlice { 0, 72, 80 }, InputSlice { 1, 72, 80 } }), BoundOperation(&Operation24, { InputSlice { 0, 80, 88 }, InputSlice { 1, 80, 88 } }), BoundOperation(&Operation24, { InputSlice { 0, 88, 96 }, InputSlice { 1, 88, 96 } }), BoundOperation(&Operation24, { InputSlice { 0, 96, 104 }, InputSlice { 1, 96, 104 } }), BoundOperation(&Operation24, { InputSlice { 0, 104, 112 }, InputSlice { 1, 104, 112 } }), BoundOperation(&Operation24, { InputSlice { 0, 112, 120 }, InputSlice { 1, 112, 120 } }), BoundOperation(&Operation24, { InputSlice { 0, 120, 128 }, InputSlice { 1, 120, 128 } }) }, 1),
InstBinding("vqaddq_s16", {  }, InstSignature { { 128, 128 }, { 128 }, false }, { BoundOperation(&Operation25, { InputSlice { 0, 0, 16 }, InputSlice { 1, 0, 16 } }), BoundOperation(&Operation25, { InputSlice { 0, 16, 32 }, InputSlice { 1, 16, 32 } }), BoundOperation(&Operation25, { InputSlice { 0, 32, 48 }, InputSlice { 1, 32, 48 } }), BoundOperation(&Operation25, { InputSlice { 0, 48, 64 }, InputSlice { 1, 48, 64 } }), BoundOperation(&Operation25, { InputSlice { 0, 64, 80 }, InputSlice { 1, 64, 80 } }), BoundOperation(&Operation25, { InputSlice { 0, 80, 96 }, InputSlice { 1, 80, 96 } }), BoundOperation(&Operation25, { InputSlice { 0, 96, 112 }, InputSlice { 1, 96, 112 } }), BoundOperation(&Operation25, { InputSlice { 0, 112, 128 }, InputSlice { 1, 112, 128 } }) }, 1),
InstBinding("vqaddq_s32", {  }, InstSignature { { 128, 128 }, { 128 }, false }, { BoundOperation(&Operation26, { InputSlice { 0, 0, 32 }, InputSlice { 1, 0, 32 } }), BoundOperation(&Operation26, { InputSlice { 0, 32, 64 }, InputSlice { 1, 32, 64 } }), BoundOperation(&Operation26, { InputSlice { 0, 64, 96 }, InputSlice { 1, 64, 96 } }), BoundOperation(&Operation26, { InputSlice { 0, 96, 128 }, InputSlice { 1, 96, 128 } }) }, 1),
InstBinding("vqaddq_u8", {  }, InstSignature { { 128, 128 }, { 128 }, false }, { BoundOperation(&Operation27, { InputSlice { 1, 0, 8 }, InputSlice { 0, 0, 8 } }), BoundOperation(&Operation27, { InputSlice { 1, 8, 16 }, InputSlice { 0, 8, 16 } }), BoundOperation(&Operation27, { InputSlice { 1, 16, 24 }, InputSlice { 0, 16, 24 } }), BoundOperation(&Operation27, { InputSlice { 1, 24, 32 }, InputSlice { 0, 24, 32 } }), BoundOperation(&Operation27, { InputSlice { 1, 32, 40 }, InputSlice { 0, 32, 40 } }), BoundOperation(&Operation27, { InputSlice { 1, 40, 48 }, InputSlice { 0, 40, 48 } }), BoundOperation(&Operation27, { InputSlice { 1, 48, 56 }, InputSlice { 0, 48, 56 } }), BoundOperation(&Operation27, { InputSlice { 1, 56, 64 }, InputSlice { 0, 56, 64 } }), BoundOperation(&Operation27, { InputSlice { 1, 64, 72 }, InputSlice { 0, 64, 72 } }), BoundOperation(&Operation27, { InputSlice { 1, 72, 80 }, InputSlice { 0, 72, 80 } }), BoundOperation(&Operation27, { InputSlice { 1, 80, 88 }, InputSlice { 0, 80, 88 } }), BoundOperation(&Operation27, { InputSlice { 1, 88, 96 }, InputSlice { 0, 88, 96 } }), BoundOperation(&Operation27, { InputSlice { 1, 96, 104 }, InputSlice { 0, 96, 104 } }), BoundOperation(&Operation27, { InputSlice { 1, 104, 112 }, InputSlice { 0, 104, 112 } }), BoundOperation(&Operation27, { InputSlice { 1, 112, 120 }, InputSlice { 0, 112, 120 } }), BoundOperation(&Operation27, { InputSlice { 1, 120, 128 }, InputSlice { 0, 120, 128 } }) }, 1),
InstBinding("vqaddq_u16", {  }, InstSignature { { 128, 128 }, { 128 }, false }, { BoundOperation(&Operation28, { InputSlice { 1, 0, 16 }, InputSlice { 0, 0, 16 } }), BoundOperation(&Operation28, { InputSlice { 1, 16, 32 }, InputSlice { 0, 16, 32 } }), BoundOperation(&Operation28, { InputSlice { 1, 32, 48 }, InputSlice { 0, 32, 48 } }), BoundOperation(&Operation28, { InputSlice { 1, 48, 64 }, InputSlice { 0, 48, 64 } }), BoundOperation(&Operation28, { InputSlice { 1, 64, 80 }, InputSlice { 0, 64, 80 } }), BoundOperation(&Operation28, { InputSlice { 1, 80, 96 }, InputSlice { 0, 80, 96 } }), BoundOperation(&Operation28, { InputSlice { 1, 96, 112 }, InputSlice { 0, 96, 112 } }), BoundOperation(&Operation28, { InputSlice { 1, 112, 128 }, InputSlice { 0, 112, 128 } }) }, 1),
InstBinding("vqaddq_u32", {  }, InstSignature { { 128, 128 }, { 128 }, false }, { BoundOperation(&Operation29, { InputSlice { 1, 0, 32 }, InputSlice { 0, 0, 32 } }), BoundOperation(&Operation29, { InputSlice { 1, 32, 64 }, InputSlice { 0, 32, 64 } }), BoundOperation(&Operation29, { InputSlice { 1, 64, 96 }, InputSlice { 0, 64, 96 } }), BoundOperation(&Operation29, { InputSlice { 1, 96, 128 }, InputSlice { 0, 96, 128 } }) }, 1),
InstBinding("vaddhn_s16", {  }, InstSignature { { 128, 128 }, { 64 }, false }, { BoundOperation(&Operation30, { InputSlice { 1, 0, 16 }, InputSlice { 0, 0, 16 } }), BoundOperation(&Operation30, { InputSlice { 1, 16, 32 }, InputSlice { 0, 16, 32 } }), BoundOperation(&Operation30, { InputSlice { 1, 32, 48 }, InputSlice { 0, 32, 48 } }), BoundOperation(&Operation30, { InputSlice { 1, 48, 64 }, InputSlice { 0, 48, 64 } }), BoundOperation(&Operation30, { InputSlice { 1, 64, 80 }, InputSlice { 0, 64, 80 } }), BoundOperation(&Operation30, { InputSlice { 1, 80, 96 }, InputSlice { 0, 80, 96 } }), BoundOperation(&Operation30, { InputSlice { 1, 96, 112 }, InputSlice { 0, 96, 112 } }), BoundOperation(&Operation30, { InputSlice { 1, 112, 128 }, InputSlice { 0, 112, 128 } }) }, 1),
InstBinding("vaddhn_s32", {  }, InstSignature { { 128, 128 }, { 64 }, false }, { BoundOperation(&Operation31, { InputSlice { 1, 0, 32 }, InputSlice { 0, 0, 32 } }), BoundOperation(&Operation31, { InputSlice { 1, 32, 64 }, InputSlice { 0, 32, 64 } }), BoundOperation(&Operation31, { InputSlice { 1, 64, 96 }, InputSlice { 0, 64, 96 } }), BoundOperation(&Operation31, { InputSlice { 1, 96, 128 }, InputSlice { 0, 96, 128 } }) }, 1),
InstBinding("vaddhn_u16", {  }, InstSignature { { 128, 128 }, { 64 }, false }, { BoundOperation(&Operation30, { InputSlice { 1, 0, 16 }, InputSlice { 0, 0, 16 } }), BoundOperation(&Operation30, { InputSlice { 1, 16, 32 }, InputSlice { 0, 16, 32 } }), BoundOperation(&Operation30, { InputSlice { 1, 32, 48 }, InputSlice { 0, 32, 48 } }), BoundOperation(&Operation30, { InputSlice { 1, 48, 64 }, InputSlice { 0, 48, 64 } }), BoundOperation(&Operation30, { InputSlice { 1, 64, 80 }, InputSlice { 0, 64, 80 } }), BoundOperation(&Operation30, { InputSlice { 1, 80, 96 }, InputSlice { 0, 80, 96 } }), BoundOperation(&Operation30, { InputSlice { 1, 96, 112 }, InputSlice { 0, 96, 112 } }), BoundOperation(&Operation30, { InputSlice { 1, 112, 128 }, InputSlice { 0, 112, 128 } }) }, 1),
InstBinding("vaddhn_u32", {  }, InstSignature { { 128, 128 }, { 64 }, false }, { BoundOperation(&Operation31, { InputSlice { 1, 0, 32 }, InputSlice { 0, 0, 32 } }), BoundOperation(&Operation31, { InputSlice { 1, 32, 64 }, InputSlice { 0, 32, 64 } }), BoundOperation(&Operation31, { InputSlice { 1, 64, 96 }, InputSlice { 0, 64, 96 } }), BoundOperation(&Operation31, { InputSlice { 1, 96, 128 }, InputSlice { 0, 96, 128 } }) }, 1),
InstBinding("vraddhn_s16", {  }, InstSignature { { 128, 128 }, { 64 }, false }, { BoundOperation(&Operation32, { InputSlice { 0, 0, 16 }, InputSlice { 1, 0, 16 } }), BoundOperation(&Operation32, { InputSlice { 0, 16, 32 }, InputSlice { 1, 16, 32 } }), BoundOperation(&Operation32, { InputSlice { 0, 32, 48 }, InputSlice { 1, 32, 48 } }), BoundOperation(&Operation32, { InputSlice { 0, 48, 64 }, InputSlice { 1, 48, 64 } }), BoundOperation(&Operation32, { InputSlice { 0, 64, 80 }, InputSlice { 1, 64, 80 } }), BoundOperation(&Operation32, { InputSlice { 0, 80, 96 }, InputSlice { 1, 80, 96 } }), BoundOperation(&Operation32, { InputSlice { 0, 96, 112 }, InputSlice { 1, 96, 112 } }), BoundOperation(&Operation32, { InputSlice { 0, 112, 128 }, InputSlice { 1, 112, 128 } }) }, 1),
InstBinding("vraddhn_s32", {  }, InstSignature { { 128, 128 }, { 64 }, false }, { BoundOperation(&Operation33, { InputSlice { 0, 0, 32 }, InputSlice { 1, 0, 32 } }), BoundOperation(&Operation33, { InputSlice { 0, 32, 64 }, InputSlice { 1, 32, 64 } }), BoundOperation(&Operation33, { InputSlice { 0, 64, 96 }, InputSlice { 1, 64, 96 } }), BoundOperation(&Operation33, { InputSlice { 0, 96, 128 }, InputSlice { 1, 96, 128 } }) }, 1),
InstBinding("vraddhn_u16", {  }, InstSignature { { 128, 128 }, { 64 }, false }, { BoundOperation(&Operation32, { InputSlice { 0, 0, 16 }, InputSlice { 1, 0, 16 } }), BoundOperation(&Operation32, { InputSlice { 0, 16, 32 }, InputSlice { 1, 16, 32 } }), BoundOperation(&Operation32, { InputSlice { 0, 32, 48 }, InputSlice { 1, 32, 48 } }), BoundOperation(&Operation32, { InputSlice { 0, 48, 64 }, InputSlice { 1, 48, 64 } }), BoundOperation(&Operation32, { InputSlice { 0, 64, 80 }, InputSlice { 1, 64, 80 } }), BoundOperation(&Operation32, { InputSlice { 0, 80, 96 }, InputSlice { 1, 80, 96 } }), BoundOperation(&Operation32, { InputSlice { 0, 96, 112 }, InputSlice { 1, 96, 112 } }), BoundOperation(&Operation32, { InputSlice { 0, 112, 128 }, InputSlice { 1, 112, 128 } }) }, 1),
InstBinding("vraddhn_u32", {  }, InstSignature { { 128, 128 }, { 64 }, false }, { BoundOperation(&Operation33, { InputSlice { 0, 0, 32 }, InputSlice { 1, 0, 32 } }), BoundOperation(&Operation33, { InputSlice { 0, 32, 64 }, InputSlice { 1, 32, 64 } }), BoundOperation(&Operation33, { InputSlice { 0, 64, 96 }, InputSlice { 1, 64, 96 } }), BoundOperation(&Operation33, { InputSlice { 0, 96, 128 }, InputSlice { 1, 96, 128 } }) }, 1),
InstBinding("vmul_s8", {  }, InstSignature { { 64, 64 }, { 64 }, false }, { BoundOperation(&Operation34, { InputSlice { 1, 0, 8 }, InputSlice { 0, 0, 8 } }), BoundOperation(&Operation34, { InputSlice { 1, 8, 16 }, InputSlice { 0, 8, 16 } }), BoundOperation(&Operation34, { InputSlice { 1, 16, 24 }, InputSlice { 0, 16, 24 } }), BoundOperation(&Operation34, { InputSlice { 1, 24, 32 }, InputSlice { 0, 24, 32 } }), BoundOperation(&Operation34, { InputSlice { 1, 32, 40 }, InputSlice { 0, 32, 40 } }), BoundOperation(&Operation34, { InputSlice { 1, 40, 48 }, InputSlice { 0, 40, 48 } }), BoundOperation(&Operation34, { InputSlice { 1, 48, 56 }, InputSlice { 0, 48, 56 } }), BoundOperation(&Operation34, { InputSlice { 1, 56, 64 }, InputSlice { 0, 56, 64 } }) }, 1),
InstBinding("vmul_s16", {  }, InstSignature { { 64, 64 }, { 64 }, false }, { BoundOperation(&Operation35, { InputSlice { 1, 0, 16 }, InputSlice { 0, 0, 16 } }), BoundOperation(&Operation35, { InputSlice { 1, 16, 32 }, InputSlice { 0, 16, 32 } }), BoundOperation(&Operation35, { InputSlice { 1, 32, 48 }, InputSlice { 0, 32, 48 } }), BoundOperation(&Operation35, { InputSlice { 1, 48, 64 }, InputSlice { 0, 48, 64 } }) }, 1),
InstBinding("vmul_s32", {  }, InstSignature { { 64, 64 }, { 64 }, false }, { BoundOperation(&Operation36, { InputSlice { 1, 0, 32 }, InputSlice { 0, 0, 32 } }), BoundOperation(&Operation36, { InputSlice { 1, 32, 64 }, InputSlice { 0, 32, 64 } }) }, 1),
InstBinding("vmul_f32", {  }, InstSignature { { 64, 64 }, { 64 }, false }, { BoundOperation(&Operation37, { InputSlice { 0, 0, 32 }, InputSlice { 1, 0, 32 } }), BoundOperation(&Operation37, { InputSlice { 0, 32, 64 }, InputSlice { 1, 32, 64 } }) }, 1),
InstBinding("vmul_u8", {  }, InstSignature { { 64, 64 }, { 64 }, false }, { BoundOperation(&Operation34, { InputSlice { 1, 0, 8 }, InputSlice { 0, 0, 8 } }), BoundOperation(&Operation34, { InputSlice { 1, 8, 16 }, InputSlice { 0, 8, 16 } }), BoundOperation(&Operation34, { InputSlice { 1, 16, 24 }, InputSlice { 0, 16, 24 } }), BoundOperation(&Operation34, { InputSlice { 1, 24, 32 }, InputSlice { 0, 24, 32 } }), BoundOperation(&Operation34, { InputSlice { 1, 32, 40 }, InputSlice { 0, 32, 40 } }), BoundOperation(&Operation34, { InputSlice { 1, 40, 48 }, InputSlice { 0, 40, 48 } }), BoundOperation(&Operation34, { InputSlice { 1, 48, 56 }, InputSlice { 0, 48, 56 } }), BoundOperation(&Operation34, { InputSlice { 1, 56, 64 }, InputSlice { 0, 56, 64 } }) }, 1),
InstBinding("vmul_u16", {  }, InstSignature { { 64, 64 }, { 64 }, false }, { BoundOperation(&Operation35, { InputSlice { 1, 0, 16 }, InputSlice { 0, 0, 16 } }), BoundOperation(&Operation35, { InputSlice { 1, 16, 32 }, InputSlice { 0, 16, 32 } }), BoundOperation(&Operation35, { InputSlice { 1, 32, 48 }, InputSlice { 0, 32, 48 } }), BoundOperation(&Operation35, { InputSlice { 1, 48, 64 }, InputSlice { 0, 48, 64 } }) }, 1),
InstBinding("vmul_u32", {  }, InstSignature { { 64, 64 }, { 64 }, false }, { BoundOperation(&Operation36, { InputSlice { 1, 0, 32 }, InputSlice { 0, 0, 32 } }), BoundOperation(&Operation36, { InputSlice { 1, 32, 64 }, InputSlice { 0, 32, 64 } }) }, 1),
InstBinding("vmulq_s8", {  }, InstSignature { { 128, 128 }, { 128 }, false }, { BoundOperation(&Operation34, { InputSlice { 1, 0, 8 }, InputSlice { 0, 0, 8 } }), BoundOperation(&Operation34, { InputSlice { 1, 8, 16 }, InputSlice { 0, 8, 16 } }), BoundOperation(&Operation34, { InputSlice { 1, 16, 24 }, InputSlice { 0, 16, 24 } }), BoundOperation(&Operation34, { InputSlice { 1, 24, 32 }, InputSlice { 0, 24, 32 } }), BoundOperation(&Operation34, { InputSlice { 1, 32, 40 }, InputSlice { 0, 32, 40 } }), BoundOperation(&Operation34, { InputSlice { 1, 40, 48 }, InputSlice { 0, 40, 48 } }), BoundOperation(&Operation34, { InputSlice { 1, 48, 56 }, InputSlice { 0, 48, 56 } }), BoundOperation(&Operation34, { InputSlice { 1, 56, 64 }, InputSlice { 0, 56, 64 } }), BoundOperation(&Operation34, { InputSlice { 1, 64, 72 }, InputSlice { 0, 64, 72 } }), BoundOperation(&Operation34, { InputSlice { 1, 72, 80 }, InputSlice { 0, 72, 80 } }), BoundOperation(&Operation34, { InputSlice { 1, 80, 88 }, InputSlice { 0, 80, 88 } }), BoundOperation(&Operation34, { InputSlice { 1, 88, 96 }, InputSlice { 0, 88, 96 } }), BoundOperation(&Operation34, { InputSlice { 1, 96, 104 }, InputSlice { 0, 96, 104 } }), BoundOperation(&Operation34, { InputSlice { 1, 104, 112 }, InputSlice { 0, 104, 112 } }), BoundOperation(&Operation34, { InputSlice { 1, 112, 120 }, InputSlice { 0, 112, 120 } }), BoundOperation(&Operation34, { InputSlice { 1, 120, 128 }, InputSlice { 0, 120, 128 } }) }, 1),
InstBinding("vmulq_s16", {  }, InstSignature { { 128, 128 }, { 128 }, false }, { BoundOperation(&Operation35, { InputSlice { 1, 0, 16 }, InputSlice { 0, 0, 16 } }), BoundOperation(&Operation35, { InputSlice { 1, 16, 32 }, InputSlice { 0, 16, 32 } }), BoundOperation(&Operation35, { InputSlice { 1, 32, 48 }, InputSlice { 0, 32, 48 } }), BoundOperation(&Operation35, { InputSlice { 1, 48, 64 }, InputSlice { 0, 48, 64 } }), BoundOperation(&Operation35, { InputSlice { 1, 64, 80 }, InputSlice { 0, 64, 80 } }), BoundOperation(&Operation35, { InputSlice { 1, 80, 96 }, InputSlice { 0, 80, 96 } }), BoundOperation(&Operation35, { InputSlice { 1, 96, 112 }, InputSlice { 0, 96, 112 } }), BoundOperation(&Operation35, { InputSlice { 1, 112, 128 }, InputSlice { 0, 112, 128 } }) }, 1),
InstBinding("vmulq_s32", {  }, InstSignature { { 128, 128 }, { 128 }, false }, { BoundOperation(&Operation36, { InputSlice { 1, 0, 32 }, InputSlice { 0, 0, 32 } }), BoundOperation(&Operation36, { InputSlice { 1, 32, 64 }, InputSlice { 0, 32, 64 } }), BoundOperation(&Operation36, { InputSlice { 1, 64, 96 }, InputSlice { 0, 64, 96 } }), BoundOperation(&Operation36, { InputSlice { 1, 96, 128 }, InputSlice { 0, 96, 128 } }) }, 1),
InstBinding("vmulq_f32", {  }, InstSignature { { 128, 128 }, { 128 }, false }, { BoundOperation(&Operation37, { InputSlice { 0, 0, 32 }, InputSlice { 1, 0, 32 } }), BoundOperation(&Operation37, { InputSlice { 0, 32, 64 }, InputSlice { 1, 32, 64 } }), BoundOperation(&Operation37, { InputSlice { 0, 64, 96 }, InputSlice { 1, 64, 96 } }), BoundOperation(&Operation37, { InputSlice { 0, 96, 128 }, InputSlice { 1, 96, 128 } }) }, 1),
InstBinding("vmulq_u8", {  }, InstSignature { { 128, 128 }, { 128 }, false }, { BoundOperation(&Operation34, { InputSlice { 1, 0, 8 }, InputSlice { 0, 0, 8 } }), BoundOperation(&Operation34, { InputSlice { 1, 8, 16 }, InputSlice { 0, 8, 16 } }), BoundOperation(&Operation34, { InputSlice { 1, 16, 24 }, InputSlice { 0, 16, 24 } }), BoundOperation(&Operation34, { InputSlice { 1, 24, 32 }, InputSlice { 0, 24, 32 } }), BoundOperation(&Operation34, { InputSlice { 1, 32, 40 }, InputSlice { 0, 32, 40 } }), BoundOperation(&Operation34, { InputSlice { 1, 40, 48 }, InputSlice { 0, 40, 48 } }), BoundOperation(&Operation34, { InputSlice { 1, 48, 56 }, InputSlice { 0, 48, 56 } }), BoundOperation(&Operation34, { InputSlice { 1, 56, 64 }, InputSlice { 0, 56, 64 } }), BoundOperation(&Operation34, { InputSlice { 1, 64, 72 }, InputSlice { 0, 64, 72 } }), BoundOperation(&Operation34, { InputSlice { 1, 72, 80 }, InputSlice { 0, 72, 80 } }), BoundOperation(&Operation34, { InputSlice { 1, 80, 88 }, InputSlice { 0, 80, 88 } }), BoundOperation(&Operation34, { InputSlice { 1, 88, 96 }, InputSlice { 0, 88, 96 } }), BoundOperation(&Operation34, { InputSlice { 1, 96, 104 }, InputSlice { 0, 96, 104 } }), BoundOperation(&Operation34, { InputSlice { 1, 104, 112 }, InputSlice { 0, 104, 112 } }), BoundOperation(&Operation34, { InputSlice { 1, 112, 120 }, InputSlice { 0, 112, 120 } }), BoundOperation(&Operation34, { InputSlice { 1, 120, 128 }, InputSlice { 0, 120, 128 } }) }, 1),
InstBinding("vmulq_u16", {  }, InstSignature { { 128, 128 }, { 128 }, false }, { BoundOperation(&Operation35, { InputSlice { 1, 0, 16 }, InputSlice { 0, 0, 16 } }), BoundOperation(&Operation35, { InputSlice { 1, 16, 32 }, InputSlice { 0, 16, 32 } }), BoundOperation(&Operation35, { InputSlice { 1, 32, 48 }, InputSlice { 0, 32, 48 } }), BoundOperation(&Operation35, { InputSlice { 1, 48, 64 }, InputSlice { 0, 48, 64 } }), BoundOperation(&Operation35, { InputSlice { 1, 64, 80 }, InputSlice { 0, 64, 80 } }), BoundOperation(&Operation35, { InputSlice { 1, 80, 96 }, InputSlice { 0, 80, 96 } }), BoundOperation(&Operation35, { InputSlice { 1, 96, 112 }, InputSlice { 0, 96, 112 } }), BoundOperation(&Operation35, { InputSlice { 1, 112, 128 }, InputSlice { 0, 112, 128 } }) }, 1),
InstBinding("vmulq_u32", {  }, InstSignature { { 128, 128 }, { 128 }, false }, { BoundOperation(&Operation36, { InputSlice { 1, 0, 32 }, InputSlice { 0, 0, 32 } }), BoundOperation(&Operation36, { InputSlice { 1, 32, 64 }, InputSlice { 0, 32, 64 } }), BoundOperation(&Operation36, { InputSlice { 1, 64, 96 }, InputSlice { 0, 64, 96 } }), BoundOperation(&Operation36, { InputSlice { 1, 96, 128 }, InputSlice { 0, 96, 128 } }) }, 1),
InstBinding("vmull_s8", {  }, InstSignature { { 64, 64 }, { 128 }, false }, { BoundOperation(&Operation38, { InputSlice { 1, 0, 8 }, InputSlice { 0, 0, 8 } }), BoundOperation(&Operation38, { InputSlice { 1, 8, 16 }, InputSlice { 0, 8, 16 } }), BoundOperation(&Operation38, { InputSlice { 1, 16, 24 }, InputSlice { 0, 16, 24 } }), BoundOperation(&Operation38, { InputSlice { 1, 24, 32 }, InputSlice { 0, 24, 32 } }), BoundOperation(&Operation38, { InputSlice { 1, 32, 40 }, InputSlice { 0, 32, 40 } }), BoundOperation(&Operation38, { InputSlice { 1, 40, 48 }, InputSlice { 0, 40, 48 } }), BoundOperation(&Operation38, { InputSlice { 1, 48, 56 }, InputSlice { 0, 48, 56 } }), BoundOperation(&Operation38, { InputSlice { 1, 56, 64 }, InputSlice { 0, 56, 64 } }) }, 1),
InstBinding("vmull_s16", {  }, InstSignature { { 64, 64 }, { 128 }, false }, { BoundOperation(&Operation39, { InputSlice { 1, 0, 16 }, InputSlice { 0, 0, 16 } }), BoundOperation(&Operation39, { InputSlice { 1, 16, 32 }, InputSlice { 0, 16, 32 } }), BoundOperation(&Operation39, { InputSlice { 1, 32, 48 }, InputSlice { 0, 32, 48 } }), BoundOperation(&Operation39, { InputSlice { 1, 48, 64 }, InputSlice { 0, 48, 64 } }) }, 1),
InstBinding("vmull_s32", {  }, InstSignature { { 64, 64 }, { 128 }, false }, { BoundOperation(&Operation40, { InputSlice { 1, 0, 32 }, InputSlice { 0, 0, 32 } }), BoundOperation(&Operation40, { InputSlice { 1, 32, 64 }, InputSlice { 0, 32, 64 } }) }, 1),
InstBinding("vmull_u8", {  }, InstSignature { { 64, 64 }, { 128 }, false }, { BoundOperation(&Operation41, { InputSlice { 1, 0, 8 }, InputSlice { 0, 0, 8 } }), BoundOperation(&Operation41, { InputSlice { 1, 8, 16 }, InputSlice { 0, 8, 16 } }), BoundOperation(&Operation41, { InputSlice { 1, 16, 24 }, InputSlice { 0, 16, 24 } }), BoundOperation(&Operation41, { InputSlice { 1, 24, 32 }, InputSlice { 0, 24, 32 } }), BoundOperation(&Operation41, { InputSlice { 1, 32, 40 }, InputSlice { 0, 32, 40 } }), BoundOperation(&Operation41, { InputSlice { 1, 40, 48 }, InputSlice { 0, 40, 48 } }), BoundOperation(&Operation41, { InputSlice { 1, 48, 56 }, InputSlice { 0, 48, 56 } }), BoundOperation(&Operation41, { InputSlice { 1, 56, 64 }, InputSlice { 0, 56, 64 } }) }, 1),
InstBinding("vmull_u16", {  }, InstSignature { { 64, 64 }, { 128 }, false }, { BoundOperation(&Operation42, { InputSlice { 1, 0, 16 }, InputSlice { 0, 0, 16 } }), BoundOperation(&Operation42, { InputSlice { 1, 16, 32 }, InputSlice { 0, 16, 32 } }), BoundOperation(&Operation42, { InputSlice { 1, 32, 48 }, InputSlice { 0, 32, 48 } }), BoundOperation(&Operation42, { InputSlice { 1, 48, 64 }, InputSlice { 0, 48, 64 } }) }, 1),
InstBinding("vmull_u32", {  }, InstSignature { { 64, 64 }, { 128 }, false }, { BoundOperation(&Operation43, { InputSlice { 1, 0, 32 }, InputSlice { 0, 0, 32 } }), BoundOperation(&Operation43, { InputSlice { 1, 32, 64 }, InputSlice { 0, 32, 64 } }) }, 1),
InstBinding("vmla_s8", {  }, InstSignature { { 64, 64, 64 }, { 64 }, false }, { BoundOperation(&Operation44, { InputSlice { 2, 0, 8 }, InputSlice { 1, 0, 8 }, InputSlice { 0, 0, 8 } }), BoundOperation(&Operation44, { InputSlice { 2, 8, 16 }, InputSlice { 1, 8, 16 }, InputSlice { 0, 8, 16 } }), BoundOperation(&Operation44, { InputSlice { 2, 16, 24 }, InputSlice { 1, 16, 24 }, InputSlice { 0, 16, 24 } }), BoundOperation(&Operation44, { InputSlice { 2, 24, 32 }, InputSlice { 1, 24, 32 }, InputSlice { 0, 24, 32 } }), BoundOperation(&Operation44, { InputSlice { 2, 32, 40 }, InputSlice { 1, 32, 40 }, InputSlice { 0, 32, 40 } }), BoundOperation(&Operation44, { InputSlice { 2, 40, 48 }, InputSlice { 1, 40, 48 }, InputSlice { 0, 40, 48 } }), BoundOperation(&Operation44, { InputSlice { 2, 48, 56 }, InputSlice { 1, 48, 56 }, InputSlice { 0, 48, 56 } }), BoundOperation(&Operation44, { InputSlice { 2, 56, 64 }, InputSlice { 1, 56, 64 }, InputSlice { 0, 56, 64 } }) }, 1),
InstBinding("vmla_s16", {  }, InstSignature { { 64, 64, 64 }, { 64 }, false }, { BoundOperation(&Operation45, { InputSlice { 2, 0, 16 }, InputSlice { 1, 0, 16 }, InputSlice { 0, 0, 16 } }), BoundOperation(&Operation45, { InputSlice { 2, 16, 32 }, InputSlice { 1, 16, 32 }, InputSlice { 0, 16, 32 } }), BoundOperation(&Operation45, { InputSlice { 2, 32, 48 }, InputSlice { 1, 32, 48 }, InputSlice { 0, 32, 48 } }), BoundOperation(&Operation45, { InputSlice { 2, 48, 64 }, InputSlice { 1, 48, 64 }, InputSlice { 0, 48, 64 } }) }, 1),
InstBinding("vmla_s32", {  }, InstSignature { { 64, 64, 64 }, { 64 }, false }, { BoundOperation(&Operation46, { InputSlice { 2, 0, 32 }, InputSlice { 1, 0, 32 }, InputSlice { 0, 0, 32 } }), BoundOperation(&Operation46, { InputSlice { 2, 32, 64 }, InputSlice { 1, 32, 64 }, InputSlice { 0, 32, 64 } }) }, 1),
InstBinding("vmla_f32", {  }, InstSignature { { 64, 64, 64 }, { 64 }, false }, { BoundOperation(&Operation47, { InputSlice { 0, 0, 32 }, InputSlice { 1, 0, 32 }, InputSlice { 2, 0, 32 } }), BoundOperation(&Operation47, { InputSlice { 0, 32, 64 }, InputSlice { 1, 32, 64 }, InputSlice { 2, 32, 64 } }) }, 1),
InstBinding("vmla_u8", {  }, InstSignature { { 64, 64, 64 }, { 64 }, false }, { BoundOperation(&Operation44, { InputSlice { 2, 0, 8 }, InputSlice { 1, 0, 8 }, InputSlice { 0, 0, 8 } }), BoundOperation(&Operation44, { InputSlice { 2, 8, 16 }, InputSlice { 1, 8, 16 }, InputSlice { 0, 8, 16 } }), BoundOperation(&Operation44, { InputSlice { 2, 16, 24 }, InputSlice { 1, 16, 24 }, InputSlice { 0, 16, 24 } }), BoundOperation(&Operation44, { InputSlice { 2, 24, 32 }, InputSlice { 1, 24, 32 }, InputSlice { 0, 24, 32 } }), BoundOperation(&Operation44, { InputSlice { 2, 32, 40 }, InputSlice { 1, 32, 40 }, InputSlice { 0, 32, 40 } }), BoundOperation(&Operation44, { InputSlice { 2, 40, 48 }, InputSlice { 1, 40, 48 }, InputSlice { 0, 40, 48 } }), BoundOperation(&Operation44, { InputSlice { 2, 48, 56 }, InputSlice { 1, 48, 56 }, InputSlice { 0, 48, 56 } }), BoundOperation(&Operation44, { InputSlice { 2, 56, 64 }, InputSlice { 1, 56, 64 }, InputSlice { 0, 56, 64 } }) }, 1),
InstBinding("vmla_u16", {  }, InstSignature { { 64, 64, 64 }, { 64 }, false }, { BoundOperation(&Operation45, { InputSlice { 2, 0, 16 }, InputSlice { 1, 0, 16 }, InputSlice { 0, 0, 16 } }), BoundOperation(&Operation45, { InputSlice { 2, 16, 32 }, InputSlice { 1, 16, 32 }, InputSlice { 0, 16, 32 } }), BoundOperation(&Operation45, { InputSlice { 2, 32, 48 }, InputSlice { 1, 32, 48 }, InputSlice { 0, 32, 48 } }), BoundOperation(&Operation45, { InputSlice { 2, 48, 64 }, InputSlice { 1, 48, 64 }, InputSlice { 0, 48, 64 } }) }, 1),
InstBinding("vmla_u32", {  }, InstSignature { { 64, 64, 64 }, { 64 }, false }, { BoundOperation(&Operation46, { InputSlice { 2, 0, 32 }, InputSlice { 1, 0, 32 }, InputSlice { 0, 0, 32 } }), BoundOperation(&Operation46, { InputSlice { 2, 32, 64 }, InputSlice { 1, 32, 64 }, InputSlice { 0, 32, 64 } }) }, 1),
InstBinding("vmlaq_s8", {  }, InstSignature { { 128, 128, 128 }, { 128 }, false }, { BoundOperation(&Operation44, { InputSlice { 2, 0, 8 }, InputSlice { 1, 0, 8 }, InputSlice { 0, 0, 8 } }), BoundOperation(&Operation44, { InputSlice { 2, 8, 16 }, InputSlice { 1, 8, 16 }, InputSlice { 0, 8, 16 } }), BoundOperation(&Operation44, { InputSlice { 2, 16, 24 }, InputSlice { 1, 16, 24 }, InputSlice { 0, 16, 24 } }), BoundOperation(&Operation44, { InputSlice { 2, 24, 32 }, InputSlice { 1, 24, 32 }, InputSlice { 0, 24, 32 } }), BoundOperation(&Operation44, { InputSlice { 2, 32, 40 }, InputSlice { 1, 32, 40 }, InputSlice { 0, 32, 40 } }), BoundOperation(&Operation44, { InputSlice { 2, 40, 48 }, InputSlice { 1, 40, 48 }, InputSlice { 0, 40, 48 } }), BoundOperation(&Operation44, { InputSlice { 2, 48, 56 }, InputSlice { 1, 48, 56 }, InputSlice { 0, 48, 56 } }), BoundOperation(&Operation44, { InputSlice { 2, 56, 64 }, InputSlice { 1, 56, 64 }, InputSlice { 0, 56, 64 } }), BoundOperation(&Operation44, { InputSlice { 2, 64, 72 }, InputSlice { 1, 64, 72 }, InputSlice { 0, 64, 72 } }), BoundOperation(&Operation44, { InputSlice { 2, 72, 80 }, InputSlice { 1, 72, 80 }, InputSlice { 0, 72, 80 } }), BoundOperation(&Operation44, { InputSlice { 2, 80, 88 }, InputSlice { 1, 80, 88 }, InputSlice { 0, 80, 88 } }), BoundOperation(&Operation44, { InputSlice { 2, 88, 96 }, InputSlice { 1, 88, 96 }, InputSlice { 0, 88, 96 } }), BoundOperation(&Operation44, { InputSlice { 2, 96, 104 }, InputSlice { 1, 96, 104 }, InputSlice { 0, 96, 104 } }), BoundOperation(&Operation44, { InputSlice { 2, 104, 112 }, InputSlice { 1, 104, 112 }, InputSlice { 0, 104, 112 } }), BoundOperation(&Operation44, { InputSlice { 2, 112, 120 }, InputSlice { 1, 112, 120 }, InputSlice { 0, 112, 120 } }), BoundOperation(&Operation44, { InputSlice { 2, 120, 128 }, InputSlice { 1, 120, 128 }, InputSlice { 0, 120, 128 } }) }, 1),
InstBinding("vmlaq_s16", {  }, InstSignature { { 128, 128, 128 }, { 128 }, false }, { BoundOperation(&Operation45, { InputSlice { 2, 0, 16 }, InputSlice { 1, 0, 16 }, InputSlice { 0, 0, 16 } }), BoundOperation(&Operation45, { InputSlice { 2, 16, 32 }, InputSlice { 1, 16, 32 }, InputSlice { 0, 16, 32 } }), BoundOperation(&Operation45, { InputSlice { 2, 32, 48 }, InputSlice { 1, 32, 48 }, InputSlice { 0, 32, 48 } }), BoundOperation(&Operation45, { InputSlice { 2, 48, 64 }, InputSlice { 1, 48, 64 }, InputSlice { 0, 48, 64 } }), BoundOperation(&Operation45, { InputSlice { 2, 64, 80 }, InputSlice { 1, 64, 80 }, InputSlice { 0, 64, 80 } }), BoundOperation(&Operation45, { InputSlice { 2, 80, 96 }, InputSlice { 1, 80, 96 }, InputSlice { 0, 80, 96 } }), BoundOperation(&Operation45, { InputSlice { 2, 96, 112 }, InputSlice { 1, 96, 112 }, InputSlice { 0, 96, 112 } }), BoundOperation(&Operation45, { InputSlice { 2, 112, 128 }, InputSlice { 1, 112, 128 }, InputSlice { 0, 112, 128 } }) }, 1),
InstBinding("vmlaq_s32", {  }, InstSignature { { 128, 128, 128 }, { 128 }, false }, { BoundOperation(&Operation46, { InputSlice { 2, 0, 32 }, InputSlice { 1, 0, 32 }, InputSlice { 0, 0, 32 } }), BoundOperation(&Operation46, { InputSlice { 2, 32, 64 }, InputSlice { 1, 32, 64 }, InputSlice { 0, 32, 64 } }), BoundOperation(&Operation46, { InputSlice { 2, 64, 96 }, InputSlice { 1, 64, 96 }, InputSlice { 0, 64, 96 } }), BoundOperation(&Operation46, { InputSlice { 2, 96, 128 }, InputSlice { 1, 96, 128 }, InputSlice { 0, 96, 128 } }) }, 1),
InstBinding("vmlaq_f32", {  }, InstSignature { { 128, 128, 128 }, { 128 }, false }, { BoundOperation(&Operation47, { InputSlice { 0, 0, 32 }, InputSlice { 1, 0, 32 }, InputSlice { 2, 0, 32 } }), BoundOperation(&Operation47, { InputSlice { 0, 32, 64 }, InputSlice { 1, 32, 64 }, InputSlice { 2, 32, 64 } }), BoundOperation(&Operation47, { InputSlice { 0, 64, 96 }, InputSlice { 1, 64, 96 }, InputSlice { 2, 64, 96 } }), BoundOperation(&Operation47, { InputSlice { 0, 96, 128 }, InputSlice { 1, 96, 128 }, InputSlice { 2, 96, 128 } }) }, 1),
InstBinding("vmlaq_u8", {  }, InstSignature { { 128, 128, 128 }, { 128 }, false }, { BoundOperation(&Operation44, { InputSlice { 2, 0, 8 }, InputSlice { 1, 0, 8 }, InputSlice { 0, 0, 8 } }), BoundOperation(&Operation44, { InputSlice { 2, 8, 16 }, InputSlice { 1, 8, 16 }, InputSlice { 0, 8, 16 } }), BoundOperation(&Operation44, { InputSlice { 2, 16, 24 }, InputSlice { 1, 16, 24 }, InputSlice { 0, 16, 24 } }), BoundOperation(&Operation44, { InputSlice { 2, 24, 32 }, InputSlice { 1, 24, 32 }, InputSlice { 0, 24, 32 } }), BoundOperation(&Operation44, { InputSlice { 2, 32, 40 }, InputSlice { 1, 32, 40 }, InputSlice { 0, 32, 40 } }), BoundOperation(&Operation44, { InputSlice { 2, 40, 48 }, InputSlice { 1, 40, 48 }, InputSlice { 0, 40, 48 } }), BoundOperation(&Operation44, { InputSlice { 2, 48, 56 }, InputSlice { 1, 48, 56 }, InputSlice { 0, 48, 56 } }), BoundOperation(&Operation44, { InputSlice { 2, 56, 64 }, InputSlice { 1, 56, 64 }, InputSlice { 0, 56, 64 } }), BoundOperation(&Operation44, { InputSlice { 2, 64, 72 }, InputSlice { 1, 64, 72 }, InputSlice { 0, 64, 72 } }), BoundOperation(&Operation44, { InputSlice { 2, 72, 80 }, InputSlice { 1, 72, 80 }, InputSlice { 0, 72, 80 } }), BoundOperation(&Operation44, { InputSlice { 2, 80, 88 }, InputSlice { 1, 80, 88 }, InputSlice { 0, 80, 88 } }), BoundOperation(&Operation44, { InputSlice { 2, 88, 96 }, InputSlice { 1, 88, 96 }, InputSlice { 0, 88, 96 } }), BoundOperation(&Operation44, { InputSlice { 2, 96, 104 }, InputSlice { 1, 96, 104 }, InputSlice { 0, 96, 104 } }), BoundOperation(&Operation44, { InputSlice { 2, 104, 112 }, InputSlice { 1, 104, 112 }, InputSlice { 0, 104, 112 } }), BoundOperation(&Operation44, { InputSlice { 2, 112, 120 }, InputSlice { 1, 112, 120 }, InputSlice { 0, 112, 120 } }), BoundOperation(&Operation44, { InputSlice { 2, 120, 128 }, InputSlice { 1, 120, 128 }, InputSlice { 0, 120, 128 } }) }, 1),
InstBinding("vmlaq_u16", {  }, InstSignature { { 128, 128, 128 }, { 128 }, false }, { BoundOperation(&Operation45, { InputSlice { 2, 0, 16 }, InputSlice { 1, 0, 16 }, InputSlice { 0, 0, 16 } }), BoundOperation(&Operation45, { InputSlice { 2, 16, 32 }, InputSlice { 1, 16, 32 }, InputSlice { 0, 16, 32 } }), BoundOperation(&Operation45, { InputSlice { 2, 32, 48 }, InputSlice { 1, 32, 48 }, InputSlice { 0, 32, 48 } }), BoundOperation(&Operation45, { InputSlice { 2, 48, 64 }, InputSlice { 1, 48, 64 }, InputSlice { 0, 48, 64 } }), BoundOperation(&Operation45, { InputSlice { 2, 64, 80 }, InputSlice { 1, 64, 80 }, InputSlice { 0, 64, 80 } }), BoundOperation(&Operation45, { InputSlice { 2, 80, 96 }, InputSlice { 1, 80, 96 }, InputSlice { 0, 80, 96 } }), BoundOperation(&Operation45, { InputSlice { 2, 96, 112 }, InputSlice { 1, 96, 112 }, InputSlice { 0, 96, 112 } }), BoundOperation(&Operation45, { InputSlice { 2, 112, 128 }, InputSlice { 1, 112, 128 }, InputSlice { 0, 112, 128 } }) }, 1),
InstBinding("vmlaq_u32", {  }, InstSignature { { 128, 128, 128 }, { 128 }, false }, { BoundOperation(&Operation46, { InputSlice { 2, 0, 32 }, InputSlice { 1, 0, 32 }, InputSlice { 0, 0, 32 } }), BoundOperation(&Operation46, { InputSlice { 2, 32, 64 }, InputSlice { 1, 32, 64 }, InputSlice { 0, 32, 64 } }), BoundOperation(&Operation46, { InputSlice { 2, 64, 96 }, InputSlice { 1, 64, 96 }, InputSlice { 0, 64, 96 } }), BoundOperation(&Operation46, { InputSlice { 2, 96, 128 }, InputSlice { 1, 96, 128 }, InputSlice { 0, 96, 128 } }) }, 1),
InstBinding("vmlal_s8", {  }, InstSignature { { 128, 64, 64 }, { 128 }, false }, { BoundOperation(&Operation48, { InputSlice { 2, 0, 8 }, InputSlice { 1, 0, 8 }, InputSlice { 0, 0, 16 } }), BoundOperation(&Operation48, { InputSlice { 2, 8, 16 }, InputSlice { 1, 8, 16 }, InputSlice { 0, 16, 32 } }), BoundOperation(&Operation48, { InputSlice { 2, 16, 24 }, InputSlice { 1, 16, 24 }, InputSlice { 0, 32, 48 } }), BoundOperation(&Operation48, { InputSlice { 2, 24, 32 }, InputSlice { 1, 24, 32 }, InputSlice { 0, 48, 64 } }), BoundOperation(&Operation48, { InputSlice { 2, 32, 40 }, InputSlice { 1, 32, 40 }, InputSlice { 0, 64, 80 } }), BoundOperation(&Operation48, { InputSlice { 2, 40, 48 }, InputSlice { 1, 40, 48 }, InputSlice { 0, 80, 96 } }), BoundOperation(&Operation48, { InputSlice { 2, 48, 56 }, InputSlice { 1, 48, 56 }, InputSlice { 0, 96, 112 } }), BoundOperation(&Operation48, { InputSlice { 2, 56, 64 }, InputSlice { 1, 56, 64 }, InputSlice { 0, 112, 128 } }) }, 1),
InstBinding("vmlal_s16", {  }, InstSignature { { 128, 64, 64 }, { 128 }, false }, { BoundOperation(&Operation49, { InputSlice { 2, 0, 16 }, InputSlice { 1, 0, 16 }, InputSlice { 0, 0, 32 } }), BoundOperation(&Operation49, { InputSlice { 2, 16, 32 }, InputSlice { 1, 16, 32 }, InputSlice { 0, 32, 64 } }), BoundOperation(&Operation49, { InputSlice { 2, 32, 48 }, InputSlice { 1, 32, 48 }, InputSlice { 0, 64, 96 } }), BoundOperation(&Operation49, { InputSlice { 2, 48, 64 }, InputSlice { 1, 48, 64 }, InputSlice { 0, 96, 128 } }) }, 1),
InstBinding("vmlal_s32", {  }, InstSignature { { 128, 64, 64 }, { 128 }, false }, { BoundOperation(&Operation50, { InputSlice { 2, 0, 32 }, InputSlice { 1, 0, 32 }, InputSlice { 0, 0, 64 } }), BoundOperation(&Operation50, { InputSlice { 2, 32, 64 }, InputSlice { 1, 32, 64 }, InputSlice { 0, 64, 128 } }) }, 1),
InstBinding("vmlal_u8", {  }, InstSignature { { 128, 64, 64 }, { 128 }, false }, { BoundOperation(&Operation51, { InputSlice { 2, 0, 8 }, InputSlice { 1, 0, 8 }, InputSlice { 0, 0, 16 } }), BoundOperation(&Operation51, { InputSlice { 2, 8, 16 }, InputSlice { 1, 8, 16 }, InputSlice { 0, 16, 32 } }), BoundOperation(&Operation51, { InputSlice { 2, 16, 24 }, InputSlice { 1, 16, 24 }, InputSlice { 0, 32, 48 } }), BoundOperation(&Operation51, { InputSlice { 2, 24, 32 }, InputSlice { 1, 24, 32 }, InputSlice { 0, 48, 64 } }), BoundOperation(&Operation51, { InputSlice { 2, 32, 40 }, InputSlice { 1, 32, 40 }, InputSlice { 0, 64, 80 } }), BoundOperation(&Operation51, { InputSlice { 2, 40, 48 }, InputSlice { 1, 40, 48 }, InputSlice { 0, 80, 96 } }), BoundOperation(&Operation51, { InputSlice { 2, 48, 56 }, InputSlice { 1, 48, 56 }, InputSlice { 0, 96, 112 } }), BoundOperation(&Operation51, { InputSlice { 2, 56, 64 }, InputSlice { 1, 56, 64 }, InputSlice { 0, 112, 128 } }) }, 1),
InstBinding("vmlal_u16", {  }, InstSignature { { 128, 64, 64 }, { 128 }, false }, { BoundOperation(&Operation52, { InputSlice { 2, 0, 16 }, InputSlice { 1, 0, 16 }, InputSlice { 0, 0, 32 } }), BoundOperation(&Operation52, { InputSlice { 2, 16, 32 }, InputSlice { 1, 16, 32 }, InputSlice { 0, 32, 64 } }), BoundOperation(&Operation52, { InputSlice { 2, 32, 48 }, InputSlice { 1, 32, 48 }, InputSlice { 0, 64, 96 } }), BoundOperation(&Operation52, { InputSlice { 2, 48, 64 }, InputSlice { 1, 48, 64 }, InputSlice { 0, 96, 128 } }) }, 1),
InstBinding("vmlal_u32", {  }, InstSignature { { 128, 64, 64 }, { 128 }, false }, { BoundOperation(&Operation53, { InputSlice { 2, 0, 32 }, InputSlice { 1, 0, 32 }, InputSlice { 0, 0, 64 } }), BoundOperation(&Operation53, { InputSlice { 2, 32, 64 }, InputSlice { 1, 32, 64 }, InputSlice { 0, 64, 128 } }) }, 1),
InstBinding("vmls_s8", {  }, InstSignature { { 64, 64, 64 }, { 64 }, false }, { BoundOperation(&Operation54, { InputSlice { 0, 0, 8 }, InputSlice { 2, 0, 8 }, InputSlice { 1, 0, 8 } }), BoundOperation(&Operation54, { InputSlice { 0, 8, 16 }, InputSlice { 2, 8, 16 }, InputSlice { 1, 8, 16 } }), BoundOperation(&Operation54, { InputSlice { 0, 16, 24 }, InputSlice { 2, 16, 24 }, InputSlice { 1, 16, 24 } }), BoundOperation(&Operation54, { InputSlice { 0, 24, 32 }, InputSlice { 2, 24, 32 }, InputSlice { 1, 24, 32 } }), BoundOperation(&Operation54, { InputSlice { 0, 32, 40 }, InputSlice { 2, 32, 40 }, InputSlice { 1, 32, 40 } }), BoundOperation(&Operation54, { InputSlice { 0, 40, 48 }, InputSlice { 2, 40, 48 }, InputSlice { 1, 40, 48 } }), BoundOperation(&Operation54, { InputSlice { 0, 48, 56 }, InputSlice { 2, 48, 56 }, InputSlice { 1, 48, 56 } }), BoundOperation(&Operation54, { InputSlice { 0, 56, 64 }, InputSlice { 2, 56, 64 }, InputSlice { 1, 56, 64 } }) }, 1),
InstBinding("vmls_s16", {  }, InstSignature { { 64, 64, 64 }, { 64 }, false }, { BoundOperation(&Operation55, { InputSlice { 0, 0, 16 }, InputSlice { 2, 0, 16 }, InputSlice { 1, 0, 16 } }), BoundOperation(&Operation55, { InputSlice { 0, 16, 32 }, InputSlice { 2, 16, 32 }, InputSlice { 1, 16, 32 } }), BoundOperation(&Operation55, { InputSlice { 0, 32, 48 }, InputSlice { 2, 32, 48 }, InputSlice { 1, 32, 48 } }), BoundOperation(&Operation55, { InputSlice { 0, 48, 64 }, InputSlice { 2, 48, 64 }, InputSlice { 1, 48, 64 } }) }, 1),
InstBinding("vmls_s32", {  }, InstSignature { { 64, 64, 64 }, { 64 }, false }, { BoundOperation(&Operation56, { InputSlice { 0, 0, 32 }, InputSlice { 2, 0, 32 }, InputSlice { 1, 0, 32 } }), BoundOperation(&Operation56, { InputSlice { 0, 32, 64 }, InputSlice { 2, 32, 64 }, InputSlice { 1, 32, 64 } }) }, 1),
InstBinding("vmls_f32", {  }, InstSignature { { 64, 64, 64 }, { 64 }, false }, { BoundOperation(&Operation57, { InputSlice { 0, 0, 32 }, InputSlice { 1, 0, 32 }, InputSlice { 2, 0, 32 } }), BoundOperation(&Operation57, { InputSlice { 0, 32, 64 }, InputSlice { 1, 32, 64 }, InputSlice { 2, 32, 64 } }) }, 1),
InstBinding("vmls_u8", {  }, InstSignature { { 64, 64, 64 }, { 64 }, false }, { BoundOperation(&Operation54, { InputSlice { 0, 0, 8 }, InputSlice { 2, 0, 8 }, InputSlice { 1, 0, 8 } }), BoundOperation(&Operation54, { InputSlice { 0, 8, 16 }, InputSlice { 2, 8, 16 }, InputSlice { 1, 8, 16 } }), BoundOperation(&Operation54, { InputSlice { 0, 16, 24 }, InputSlice { 2, 16, 24 }, InputSlice { 1, 16, 24 } }), BoundOperation(&Operation54, { InputSlice { 0, 24, 32 }, InputSlice { 2, 24, 32 }, InputSlice { 1, 24, 32 } }), BoundOperation(&Operation54, { InputSlice { 0, 32, 40 }, InputSlice { 2, 32, 40 }, InputSlice { 1, 32, 40 } }), BoundOperation(&Operation54, { InputSlice { 0, 40, 48 }, InputSlice { 2, 40, 48 }, InputSlice { 1, 40, 48 } }), BoundOperation(&Operation54, { InputSlice { 0, 48, 56 }, InputSlice { 2, 48, 56 }, InputSlice { 1, 48, 56 } }), BoundOperation(&Operation54, { InputSlice { 0, 56, 64 }, InputSlice { 2, 56, 64 }, InputSlice { 1, 56, 64 } }) }, 1),
InstBinding("vmls_u16", {  }, InstSignature { { 64, 64, 64 }, { 64 }, false }, { BoundOperation(&Operation55, { InputSlice { 0, 0, 16 }, InputSlice { 2, 0, 16 }, InputSlice { 1, 0, 16 } }), BoundOperation(&Operation55, { InputSlice { 0, 16, 32 }, InputSlice { 2, 16, 32 }, InputSlice { 1, 16, 32 } }), BoundOperation(&Operation55, { InputSlice { 0, 32, 48 }, InputSlice { 2, 32, 48 }, InputSlice { 1, 32, 48 } }), BoundOperation(&Operation55, { InputSlice { 0, 48, 64 }, InputSlice { 2, 48, 64 }, InputSlice { 1, 48, 64 } }) }, 1),
InstBinding("vmls_u32", {  }, InstSignature { { 64, 64, 64 }, { 64 }, false }, { BoundOperation(&Operation56, { InputSlice { 0, 0, 32 }, InputSlice { 2, 0, 32 }, InputSlice { 1, 0, 32 } }), BoundOperation(&Operation56, { InputSlice { 0, 32, 64 }, InputSlice { 2, 32, 64 }, InputSlice { 1, 32, 64 } }) }, 1),
InstBinding("vmlsq_s8", {  }, InstSignature { { 128, 128, 128 }, { 128 }, false }, { BoundOperation(&Operation54, { InputSlice { 0, 0, 8 }, InputSlice { 2, 0, 8 }, InputSlice { 1, 0, 8 } }), BoundOperation(&Operation54, { InputSlice { 0, 8, 16 }, InputSlice { 2, 8, 16 }, InputSlice { 1, 8, 16 } }), BoundOperation(&Operation54, { InputSlice { 0, 16, 24 }, InputSlice { 2, 16, 24 }, InputSlice { 1, 16, 24 } }), BoundOperation(&Operation54, { InputSlice { 0, 24, 32 }, InputSlice { 2, 24, 32 }, InputSlice { 1, 24, 32 } }), BoundOperation(&Operation54, { InputSlice { 0, 32, 40 }, InputSlice { 2, 32, 40 }, InputSlice { 1, 32, 40 } }), BoundOperation(&Operation54, { InputSlice { 0, 40, 48 }, InputSlice { 2, 40, 48 }, InputSlice { 1, 40, 48 } }), BoundOperation(&Operation54, { InputSlice { 0, 48, 56 }, InputSlice { 2, 48, 56 }, InputSlice { 1, 48, 56 } }), BoundOperation(&Operation54, { InputSlice { 0, 56, 64 }, InputSlice { 2, 56, 64 }, InputSlice { 1, 56, 64 } }), BoundOperation(&Operation54, { InputSlice { 0, 64, 72 }, InputSlice { 2, 64, 72 }, InputSlice { 1, 64, 72 } }), BoundOperation(&Operation54, { InputSlice { 0, 72, 80 }, InputSlice { 2, 72, 80 }, InputSlice { 1, 72, 80 } }), BoundOperation(&Operation54, { InputSlice { 0, 80, 88 }, InputSlice { 2, 80, 88 }, InputSlice { 1, 80, 88 } }), BoundOperation(&Operation54, { InputSlice { 0, 88, 96 }, InputSlice { 2, 88, 96 }, InputSlice { 1, 88, 96 } }), BoundOperation(&Operation54, { InputSlice { 0, 96, 104 }, InputSlice { 2, 96, 104 }, InputSlice { 1, 96, 104 } }), BoundOperation(&Operation54, { InputSlice { 0, 104, 112 }, InputSlice { 2, 104, 112 }, InputSlice { 1, 104, 112 } }), BoundOperation(&Operation54, { InputSlice { 0, 112, 120 }, InputSlice { 2, 112, 120 }, InputSlice { 1, 112, 120 } }), BoundOperation(&Operation54, { InputSlice { 0, 120, 128 }, InputSlice { 2, 120, 128 }, InputSlice { 1, 120, 128 } }) }, 1),
InstBinding("vmlsq_s16", {  }, InstSignature { { 128, 128, 128 }, { 128 }, false }, { BoundOperation(&Operation55, { InputSlice { 0, 0, 16 }, InputSlice { 2, 0, 16 }, InputSlice { 1, 0, 16 } }), BoundOperation(&Operation55, { InputSlice { 0, 16, 32 }, InputSlice { 2, 16, 32 }, InputSlice { 1, 16, 32 } }), BoundOperation(&Operation55, { InputSlice { 0, 32, 48 }, InputSlice { 2, 32, 48 }, InputSlice { 1, 32, 48 } }), BoundOperation(&Operation55, { InputSlice { 0, 48, 64 }, InputSlice { 2, 48, 64 }, InputSlice { 1, 48, 64 } }), BoundOperation(&Operation55, { InputSlice { 0, 64, 80 }, InputSlice { 2, 64, 80 }, InputSlice { 1, 64, 80 } }), BoundOperation(&Operation55, { InputSlice { 0, 80, 96 }, InputSlice { 2, 80, 96 }, InputSlice { 1, 80, 96 } }), BoundOperation(&Operation55, { InputSlice { 0, 96, 112 }, InputSlice { 2, 96, 112 }, InputSlice { 1, 96, 112 } }), BoundOperation(&Operation55, { InputSlice { 0, 112, 128 }, InputSlice { 2, 112, 128 }, InputSlice { 1, 112, 128 } }) }, 1),
InstBinding("vmlsq_s32", {  }, InstSignature { { 128, 128, 128 }, { 128 }, false }, { BoundOperation(&Operation56, { InputSlice { 0, 0, 32 }, InputSlice { 2, 0, 32 }, InputSlice { 1, 0, 32 } }), BoundOperation(&Operation56, { InputSlice { 0, 32, 64 }, InputSlice { 2, 32, 64 }, InputSlice { 1, 32, 64 } }), BoundOperation(&Operation56, { InputSlice { 0, 64, 96 }, InputSlice { 2, 64, 96 }, InputSlice { 1, 64, 96 } }), BoundOperation(&Operation56, { InputSlice { 0, 96, 128 }, InputSlice { 2, 96, 128 }, InputSlice { 1, 96, 128 } }) }, 1),
InstBinding("vmlsq_f32", {  }, InstSignature { { 128, 128, 128 }, { 128 }, false }, { BoundOperation(&Operation57, { InputSlice { 0, 0, 32 }, InputSlice { 1, 0, 32 }, InputSlice { 2, 0, 32 } }), BoundOperation(&Operation57, { InputSlice { 0, 32, 64 }, InputSlice { 1, 32, 64 }, InputSlice { 2, 32, 64 } }), BoundOperation(&Operation57, { InputSlice { 0, 64, 96 }, InputSlice { 1, 64, 96 }, InputSlice { 2, 64, 96 } }), BoundOperation(&Operation57, { InputSlice { 0, 96, 128 }, InputSlice { 1, 96, 128 }, InputSlice { 2, 96, 128 } }) }, 1),
InstBinding("vmlsq_u8", {  }, InstSignature { { 128, 128, 128 }, { 128 }, false }, { BoundOperation(&Operation54, { InputSlice { 0, 0, 8 }, InputSlice { 2, 0, 8 }, InputSlice { 1, 0, 8 } }), BoundOperation(&Operation54, { InputSlice { 0, 8, 16 }, InputSlice { 2, 8, 16 }, InputSlice { 1, 8, 16 } }), BoundOperation(&Operation54, { InputSlice { 0, 16, 24 }, InputSlice { 2, 16, 24 }, InputSlice { 1, 16, 24 } }), BoundOperation(&Operation54, { InputSlice { 0, 24, 32 }, InputSlice { 2, 24, 32 }, InputSlice { 1, 24, 32 } }), BoundOperation(&Operation54, { InputSlice { 0, 32, 40 }, InputSlice { 2, 32, 40 }, InputSlice { 1, 32, 40 } }), BoundOperation(&Operation54, { InputSlice { 0, 40, 48 }, InputSlice { 2, 40, 48 }, InputSlice { 1, 40, 48 } }), BoundOperation(&Operation54, { InputSlice { 0, 48, 56 }, InputSlice { 2, 48, 56 }, InputSlice { 1, 48, 56 } }), BoundOperation(&Operation54, { InputSlice { 0, 56, 64 }, InputSlice { 2, 56, 64 }, InputSlice { 1, 56, 64 } }), BoundOperation(&Operation54, { InputSlice { 0, 64, 72 }, InputSlice { 2, 64, 72 }, InputSlice { 1, 64, 72 } }), BoundOperation(&Operation54, { InputSlice { 0, 72, 80 }, InputSlice { 2, 72, 80 }, InputSlice { 1, 72, 80 } }), BoundOperation(&Operation54, { InputSlice { 0, 80, 88 }, InputSlice { 2, 80, 88 }, InputSlice { 1, 80, 88 } }), BoundOperation(&Operation54, { InputSlice { 0, 88, 96 }, InputSlice { 2, 88, 96 }, InputSlice { 1, 88, 96 } }), BoundOperation(&Operation54, { InputSlice { 0, 96, 104 }, InputSlice { 2, 96, 104 }, InputSlice { 1, 96, 104 } }), BoundOperation(&Operation54, { InputSlice { 0, 104, 112 }, InputSlice { 2, 104, 112 }, InputSlice { 1, 104, 112 } }), BoundOperation(&Operation54, { InputSlice { 0, 112, 120 }, InputSlice { 2, 112, 120 }, InputSlice { 1, 112, 120 } }), BoundOperation(&Operation54, { InputSlice { 0, 120, 128 }, InputSlice { 2, 120, 128 }, InputSlice { 1, 120, 128 } }) }, 1),
InstBinding("vmlsq_u16", {  }, InstSignature { { 128, 128, 128 }, { 128 }, false }, { BoundOperation(&Operation55, { InputSlice { 0, 0, 16 }, InputSlice { 2, 0, 16 }, InputSlice { 1, 0, 16 } }), BoundOperation(&Operation55, { InputSlice { 0, 16, 32 }, InputSlice { 2, 16, 32 }, InputSlice { 1, 16, 32 } }), BoundOperation(&Operation55, { InputSlice { 0, 32, 48 }, InputSlice { 2, 32, 48 }, InputSlice { 1, 32, 48 } }), BoundOperation(&Operation55, { InputSlice { 0, 48, 64 }, InputSlice { 2, 48, 64 }, InputSlice { 1, 48, 64 } }), BoundOperation(&Operation55, { InputSlice { 0, 64, 80 }, InputSlice { 2, 64, 80 }, InputSlice { 1, 64, 80 } }), BoundOperation(&Operation55, { InputSlice { 0, 80, 96 }, InputSlice { 2, 80, 96 }, InputSlice { 1, 80, 96 } }), BoundOperation(&Operation55, { InputSlice { 0, 96, 112 }, InputSlice { 2, 96, 112 }, InputSlice { 1, 96, 112 } }), BoundOperation(&Operation55, { InputSlice { 0, 112, 128 }, InputSlice { 2, 112, 128 }, InputSlice { 1, 112, 128 } }) }, 1),
InstBinding("vmlsq_u32", {  }, InstSignature { { 128, 128, 128 }, { 128 }, false }, { BoundOperation(&Operation56, { InputSlice { 0, 0, 32 }, InputSlice { 2, 0, 32 }, InputSlice { 1, 0, 32 } }), BoundOperation(&Operation56, { InputSlice { 0, 32, 64 }, InputSlice { 2, 32, 64 }, InputSlice { 1, 32, 64 } }), BoundOperation(&Operation56, { InputSlice { 0, 64, 96 }, InputSlice { 2, 64, 96 }, InputSlice { 1, 64, 96 } }), BoundOperation(&Operation56, { InputSlice { 0, 96, 128 }, InputSlice { 2, 96, 128 }, InputSlice { 1, 96, 128 } }) }, 1),
InstBinding("vmlsl_s8", {  }, InstSignature { { 128, 64, 64 }, { 128 }, false }, { BoundOperation(&Operation58, { InputSlice { 0, 0, 16 }, InputSlice { 2, 0, 8 }, InputSlice { 1, 0, 8 } }), BoundOperation(&Operation58, { InputSlice { 0, 16, 32 }, InputSlice { 2, 8, 16 }, InputSlice { 1, 8, 16 } }), BoundOperation(&Operation58, { InputSlice { 0, 32, 48 }, InputSlice { 2, 16, 24 }, InputSlice { 1, 16, 24 } }), BoundOperation(&Operation58, { InputSlice { 0, 48, 64 }, InputSlice { 2, 24, 32 }, InputSlice { 1, 24, 32 } }), BoundOperation(&Operation58, { InputSlice { 0, 64, 80 }, InputSlice { 2, 32, 40 }, InputSlice { 1, 32, 40 } }), BoundOperation(&Operation58, { InputSlice { 0, 80, 96 }, InputSlice { 2, 40, 48 }, InputSlice { 1, 40, 48 } }), BoundOperation(&Operation58, { InputSlice { 0, 96, 112 }, InputSlice { 2, 48, 56 }, InputSlice { 1, 48, 56 } }), BoundOperation(&Operation58, { InputSlice { 0, 112, 128 }, InputSlice { 2, 56, 64 }, InputSlice { 1, 56, 64 } }) }, 1),
InstBinding("vmlsl_s16", {  }, InstSignature { { 128, 64, 64 }, { 128 }, false }, { BoundOperation(&Operation59, { InputSlice { 0, 0, 32 }, InputSlice { 2, 0, 16 }, InputSlice { 1, 0, 16 } }), BoundOperation(&Operation59, { InputSlice { 0, 32, 64 }, InputSlice { 2, 16, 32 }, InputSlice { 1, 16, 32 } }), BoundOperation(&Operation59, { InputSlice { 0, 64, 96 }, InputSlice { 2, 32, 48 }, InputSlice { 1, 32, 48 } }), BoundOperation(&Operation59, { InputSlice { 0, 96, 128 }, InputSlice { 2, 48, 64 }, InputSlice { 1, 48, 64 } }) }, 1),
InstBinding("vmlsl_s32", {  }, InstSignature { { 128, 64, 64 }, { 128 }, false }, { BoundOperation(&Operation60, { InputSlice { 0, 0, 64 }, InputSlice { 2, 0, 32 }, InputSlice { 1, 0, 32 } }), BoundOperation(&Operation60, { InputSlice { 0, 64, 128 }, InputSlice { 2, 32, 64 }, InputSlice { 1, 32, 64 } }) }, 1),
InstBinding("vmlsl_u8", {  }, InstSignature { { 128, 64, 64 }, { 128 }, false }, { BoundOperation(&Operation61, { InputSlice { 0, 0, 16 }, InputSlice { 2, 0, 8 }, InputSlice { 1, 0, 8 } }), BoundOperation(&Operation61, { InputSlice { 0, 16, 32 }, InputSlice { 2, 8, 16 }, InputSlice { 1, 8, 16 } }), BoundOperation(&Operation61, { InputSlice { 0, 32, 48 }, InputSlice { 2, 16, 24 }, InputSlice { 1, 16, 24 } }), BoundOperation(&Operation61, { InputSlice { 0, 48, 64 }, InputSlice { 2, 24, 32 }, InputSlice { 1, 24, 32 } }), BoundOperation(&Operation61, { InputSlice { 0, 64, 80 }, InputSlice { 2, 32, 40 }, InputSlice { 1, 32, 40 } }), BoundOperation(&Operation61, { InputSlice { 0, 80, 96 }, InputSlice { 2, 40, 48 }, InputSlice { 1, 40, 48 } }), BoundOperation(&Operation61, { InputSlice { 0, 96, 112 }, InputSlice { 2, 48, 56 }, InputSlice { 1, 48, 56 } }), BoundOperation(&Operation61, { InputSlice { 0, 112, 128 }, InputSlice { 2, 56, 64 }, InputSlice { 1, 56, 64 } }) }, 1),
InstBinding("vmlsl_u16", {  }, InstSignature { { 128, 64, 64 }, { 128 }, false }, { BoundOperation(&Operation62, { InputSlice { 0, 0, 32 }, InputSlice { 2, 0, 16 }, InputSlice { 1, 0, 16 } }), BoundOperation(&Operation62, { InputSlice { 0, 32, 64 }, InputSlice { 2, 16, 32 }, InputSlice { 1, 16, 32 } }), BoundOperation(&Operation62, { InputSlice { 0, 64, 96 }, InputSlice { 2, 32, 48 }, InputSlice { 1, 32, 48 } }), BoundOperation(&Operation62, { InputSlice { 0, 96, 128 }, InputSlice { 2, 48, 64 }, InputSlice { 1, 48, 64 } }) }, 1),
InstBinding("vmlsl_u32", {  }, InstSignature { { 128, 64, 64 }, { 128 }, false }, { BoundOperation(&Operation63, { InputSlice { 0, 0, 64 }, InputSlice { 2, 0, 32 }, InputSlice { 1, 0, 32 } }), BoundOperation(&Operation63, { InputSlice { 0, 64, 128 }, InputSlice { 2, 32, 64 }, InputSlice { 1, 32, 64 } }) }, 1),
InstBinding("vqdmulh_s16", {  }, InstSignature { { 64, 64 }, { 64 }, false }, { BoundOperation(&Operation64, { InputSlice { 1, 0, 16 }, InputSlice { 0, 0, 16 } }), BoundOperation(&Operation64, { InputSlice { 1, 16, 32 }, InputSlice { 0, 16, 32 } }), BoundOperation(&Operation64, { InputSlice { 1, 32, 48 }, InputSlice { 0, 32, 48 } }), BoundOperation(&Operation64, { InputSlice { 1, 48, 64 }, InputSlice { 0, 48, 64 } }) }, 1),
InstBinding("vqdmulh_s32", {  }, InstSignature { { 64, 64 }, { 64 }, false }, { BoundOperation(&Operation65, { InputSlice { 1, 0, 32 }, InputSlice { 0, 0, 32 } }), BoundOperation(&Operation65, { InputSlice { 1, 32, 64 }, InputSlice { 0, 32, 64 } }) }, 1),
InstBinding("vqdmulhq_s16", {  }, InstSignature { { 128, 128 }, { 128 }, false }, { BoundOperation(&Operation64, { InputSlice { 1, 0, 16 }, InputSlice { 0, 0, 16 } }), BoundOperation(&Operation64, { InputSlice { 1, 16, 32 }, InputSlice { 0, 16, 32 } }), BoundOperation(&Operation64, { InputSlice { 1, 32, 48 }, InputSlice { 0, 32, 48 } }), BoundOperation(&Operation64, { InputSlice { 1, 48, 64 }, InputSlice { 0, 48, 64 } }), BoundOperation(&Operation64, { InputSlice { 1, 64, 80 }, InputSlice { 0, 64, 80 } }), BoundOperation(&Operation64, { InputSlice { 1, 80, 96 }, InputSlice { 0, 80, 96 } }), BoundOperation(&Operation64, { InputSlice { 1, 96, 112 }, InputSlice { 0, 96, 112 } }), BoundOperation(&Operation64, { InputSlice { 1, 112, 128 }, InputSlice { 0, 112, 128 } }) }, 1),
InstBinding("vqdmulhq_s32", {  }, InstSignature { { 128, 128 }, { 128 }, false }, { BoundOperation(&Operation65, { InputSlice { 1, 0, 32 }, InputSlice { 0, 0, 32 } }), BoundOperation(&Operation65, { InputSlice { 1, 32, 64 }, InputSlice { 0, 32, 64 } }), BoundOperation(&Operation65, { InputSlice { 1, 64, 96 }, InputSlice { 0, 64, 96 } }), BoundOperation(&Operation65, { InputSlice { 1, 96, 128 }, InputSlice { 0, 96, 128 } }) }, 1),
InstBinding("vqrdmulh_s16", {  }, InstSignature { { 64, 64 }, { 64 }, false }, { BoundOperation(&Operation66, { InputSlice { 0, 0, 16 }, InputSlice { 1, 0, 16 } }), BoundOperation(&Operation66, { InputSlice { 0, 16, 32 }, InputSlice { 1, 16, 32 } }), BoundOperation(&Operation66, { InputSlice { 0, 32, 48 }, InputSlice { 1, 32, 48 } }), BoundOperation(&Operation66, { InputSlice { 0, 48, 64 }, InputSlice { 1, 48, 64 } }) }, 1),
InstBinding("vqrdmulh_s32", {  }, InstSignature { { 64, 64 }, { 64 }, false }, { BoundOperation(&Operation67, { InputSlice { 0, 0, 32 }, InputSlice { 1, 0, 32 } }), BoundOperation(&Operation67, { InputSlice { 0, 32, 64 }, InputSlice { 1, 32, 64 } }) }, 1),
InstBinding("vqrdmulhq_s16", {  }, InstSignature { { 128, 128 }, { 128 }, false }, { BoundOperation(&Operation66, { InputSlice { 0, 0, 16 }, InputSlice { 1, 0, 16 } }), BoundOperation(&Operation66, { InputSlice { 0, 16, 32 }, InputSlice { 1, 16, 32 } }), BoundOperation(&Operation66, { InputSlice { 0, 32, 48 }, InputSlice { 1, 32, 48 } }), BoundOperation(&Operation66, { InputSlice { 0, 48, 64 }, InputSlice { 1, 48, 64 } }), BoundOperation(&Operation66, { InputSlice { 0, 64, 80 }, InputSlice { 1, 64, 80 } }), BoundOperation(&Operation66, { InputSlice { 0, 80, 96 }, InputSlice { 1, 80, 96 } }), BoundOperation(&Operation66, { InputSlice { 0, 96, 112 }, InputSlice { 1, 96, 112 } }), BoundOperation(&Operation66, { InputSlice { 0, 112, 128 }, InputSlice { 1, 112, 128 } }) }, 1),
InstBinding("vqrdmulhq_s32", {  }, InstSignature { { 128, 128 }, { 128 }, false }, { BoundOperation(&Operation67, { InputSlice { 0, 0, 32 }, InputSlice { 1, 0, 32 } }), BoundOperation(&Operation67, { InputSlice { 0, 32, 64 }, InputSlice { 1, 32, 64 } }), BoundOperation(&Operation67, { InputSlice { 0, 64, 96 }, InputSlice { 1, 64, 96 } }), BoundOperation(&Operation67, { InputSlice { 0, 96, 128 }, InputSlice { 1, 96, 128 } }) }, 1),
InstBinding("vsub_s8", {  }, InstSignature { { 64, 64 }, { 64 }, false }, { BoundOperation(&Operation68, { InputSlice { 0, 0, 8 }, InputSlice { 1, 0, 8 } }), BoundOperation(&Operation68, { InputSlice { 0, 8, 16 }, InputSlice { 1, 8, 16 } }), BoundOperation(&Operation68, { InputSlice { 0, 16, 24 }, InputSlice { 1, 16, 24 } }), BoundOperation(&Operation68, { InputSlice { 0, 24, 32 }, InputSlice { 1, 24, 32 } }), BoundOperation(&Operation68, { InputSlice { 0, 32, 40 }, InputSlice { 1, 32, 40 } }), BoundOperation(&Operation68, { InputSlice { 0, 40, 48 }, InputSlice { 1, 40, 48 } }), BoundOperation(&Operation68, { InputSlice { 0, 48, 56 }, InputSlice { 1, 48, 56 } }), BoundOperation(&Operation68, { InputSlice { 0, 56, 64 }, InputSlice { 1, 56, 64 } }) }, 1),
InstBinding("vsub_s16", {  }, InstSignature { { 64, 64 }, { 64 }, false }, { BoundOperation(&Operation69, { InputSlice { 0, 0, 16 }, InputSlice { 1, 0, 16 } }), BoundOperation(&Operation69, { InputSlice { 0, 16, 32 }, InputSlice { 1, 16, 32 } }), BoundOperation(&Operation69, { InputSlice { 0, 32, 48 }, InputSlice { 1, 32, 48 } }), BoundOperation(&Operation69, { InputSlice { 0, 48, 64 }, InputSlice { 1, 48, 64 } }) }, 1),
InstBinding("vsub_s32", {  }, InstSignature { { 64, 64 }, { 64 }, false }, { BoundOperation(&Operation70, { InputSlice { 0, 0, 32 }, InputSlice { 1, 0, 32 } }), BoundOperation(&Operation70, { InputSlice { 0, 32, 64 }, InputSlice { 1, 32, 64 } }) }, 1),
InstBinding("vsub_s64", {  }, InstSignature { { 64, 64 }, { 64 }, false }, { BoundOperation(&Operation71, { InputSlice { 0, 0, 64 }, InputSlice { 1, 0, 64 } }) }, 1),
InstBinding("vsub_f32", {  }, InstSignature { { 64, 64 }, { 64 }, false }, { BoundOperation(&Operation72, { InputSlice { 0, 0, 32 }, InputSlice { 1, 0, 32 } }), BoundOperation(&Operation72, { InputSlice { 0, 32, 64 }, InputSlice { 1, 32, 64 } }) }, 1),
InstBinding("vsub_u8", {  }, InstSignature { { 64, 64 }, { 64 }, false }, { BoundOperation(&Operation68, { InputSlice { 0, 0, 8 }, InputSlice { 1, 0, 8 } }), BoundOperation(&Operation68, { InputSlice { 0, 8, 16 }, InputSlice { 1, 8, 16 } }), BoundOperation(&Operation68, { InputSlice { 0, 16, 24 }, InputSlice { 1, 16, 24 } }), BoundOperation(&Operation68, { InputSlice { 0, 24, 32 }, InputSlice { 1, 24, 32 } }), BoundOperation(&Operation68, { InputSlice { 0, 32, 40 }, InputSlice { 1, 32, 40 } }), BoundOperation(&Operation68, { InputSlice { 0, 40, 48 }, InputSlice { 1, 40, 48 } }), BoundOperation(&Operation68, { InputSlice { 0, 48, 56 }, InputSlice { 1, 48, 56 } }), BoundOperation(&Operation68, { InputSlice { 0, 56, 64 }, InputSlice { 1, 56, 64 } }) }, 1),
InstBinding("vsub_u16", {  }, InstSignature { { 64, 64 }, { 64 }, false }, { BoundOperation(&Operation69, { InputSlice { 0, 0, 16 }, InputSlice { 1, 0, 16 } }), BoundOperation(&Operation69, { InputSlice { 0, 16, 32 }, InputSlice { 1, 16, 32 } }), BoundOperation(&Operation69, { InputSlice { 0, 32, 48 }, InputSlice { 1, 32, 48 } }), BoundOperation(&Operation69, { InputSlice { 0, 48, 64 }, InputSlice { 1, 48, 64 } }) }, 1),
InstBinding("vsub_u32", {  }, InstSignature { { 64, 64 }, { 64 }, false }, { BoundOperation(&Operation70, { InputSlice { 0, 0, 32 }, InputSlice { 1, 0, 32 } }), BoundOperation(&Operation70, { InputSlice { 0, 32, 64 }, InputSlice { 1, 32, 64 } }) }, 1),
InstBinding("vsub_u64", {  }, InstSignature { { 64, 64 }, { 64 }, false }, { BoundOperation(&Operation71, { InputSlice { 0, 0, 64 }, InputSlice { 1, 0, 64 } }) }, 1),
InstBinding("vsubq_s8", {  }, InstSignature { { 128, 128 }, { 128 }, false }, { BoundOperation(&Operation68, { InputSlice { 0, 0, 8 }, InputSlice { 1, 0, 8 } }), BoundOperation(&Operation68, { InputSlice { 0, 8, 16 }, InputSlice { 1, 8, 16 } }), BoundOperation(&Operation68, { InputSlice { 0, 16, 24 }, InputSlice { 1, 16, 24 } }), BoundOperation(&Operation68, { InputSlice { 0, 24, 32 }, InputSlice { 1, 24, 32 } }), BoundOperation(&Operation68, { InputSlice { 0, 32, 40 }, InputSlice { 1, 32, 40 } }), BoundOperation(&Operation68, { InputSlice { 0, 40, 48 }, InputSlice { 1, 40, 48 } }), BoundOperation(&Operation68, { InputSlice { 0, 48, 56 }, InputSlice { 1, 48, 56 } }), BoundOperation(&Operation68, { InputSlice { 0, 56, 64 }, InputSlice { 1, 56, 64 } }), BoundOperation(&Operation68, { InputSlice { 0, 64, 72 }, InputSlice { 1, 64, 72 } }), BoundOperation(&Operation68, { InputSlice { 0, 72, 80 }, InputSlice { 1, 72, 80 } }), BoundOperation(&Operation68, { InputSlice { 0, 80, 88 }, InputSlice { 1, 80, 88 } }), BoundOperation(&Operation68, { InputSlice { 0, 88, 96 }, InputSlice { 1, 88, 96 } }), BoundOperation(&Operation68, { InputSlice { 0, 96, 104 }, InputSlice { 1, 96, 104 } }), BoundOperation(&Operation68, { InputSlice { 0, 104, 112 }, InputSlice { 1, 104, 112 } }), BoundOperation(&Operation68, { InputSlice { 0, 112, 120 }, InputSlice { 1, 112, 120 } }), BoundOperation(&Operation68, { InputSlice { 0, 120, 128 }, InputSlice { 1, 120, 128 } }) }, 1),
InstBinding("vsubq_s16", {  }, InstSignature { { 128, 128 }, { 128 }, false }, { BoundOperation(&Operation69, { InputSlice { 0, 0, 16 }, InputSlice { 1, 0, 16 } }), BoundOperation(&Operation69, { InputSlice { 0, 16, 32 }, InputSlice { 1, 16, 32 } }), BoundOperation(&Operation69, { InputSlice { 0, 32, 48 }, InputSlice { 1, 32, 48 } }), BoundOperation(&Operation69, { InputSlice { 0, 48, 64 }, InputSlice { 1, 48, 64 } }), BoundOperation(&Operation69, { InputSlice { 0, 64, 80 }, InputSlice { 1, 64, 80 } }), BoundOperation(&Operation69, { InputSlice { 0, 80, 96 }, InputSlice { 1, 80, 96 } }), BoundOperation(&Operation69, { InputSlice { 0, 96, 112 }, InputSlice { 1, 96, 112 } }), BoundOperation(&Operation69, { InputSlice { 0, 112, 128 }, InputSlice { 1, 112, 128 } }) }, 1),
InstBinding("vsubq_s32", {  }, InstSignature { { 128, 128 }, { 128 }, false }, { BoundOperation(&Operation70, { InputSlice { 0, 0, 32 }, InputSlice { 1, 0, 32 } }), BoundOperation(&Operation70, { InputSlice { 0, 32, 64 }, InputSlice { 1, 32, 64 } }), BoundOperation(&Operation70, { InputSlice { 0, 64, 96 }, InputSlice { 1, 64, 96 } }), BoundOperation(&Operation70, { InputSlice { 0, 96, 128 }, InputSlice { 1, 96, 128 } }) }, 1),
InstBinding("vsubq_s64", {  }, InstSignature { { 128, 128 }, { 128 }, false }, { BoundOperation(&Operation71, { InputSlice { 0, 0, 64 }, InputSlice { 1, 0, 64 } }), BoundOperation(&Operation71, { InputSlice { 0, 64, 128 }, InputSlice { 1, 64, 128 } }) }, 1),
InstBinding("vsubq_f32", {  }, InstSignature { { 128, 128 }, { 128 }, false }, { BoundOperation(&Operation72, { InputSlice { 0, 0, 32 }, InputSlice { 1, 0, 32 } }), BoundOperation(&Operation72, { InputSlice { 0, 32, 64 }, InputSlice { 1, 32, 64 } }), BoundOperation(&Operation72, { InputSlice { 0, 64, 96 }, InputSlice { 1, 64, 96 } }), BoundOperation(&Operation72, { InputSlice { 0, 96, 128 }, InputSlice { 1, 96, 128 } }) }, 1),
InstBinding("vsubq_u8", {  }, InstSignature { { 128, 128 }, { 128 }, false }, { BoundOperation(&Operation68, { InputSlice { 0, 0, 8 }, InputSlice { 1, 0, 8 } }), BoundOperation(&Operation68, { InputSlice { 0, 8, 16 }, InputSlice { 1, 8, 16 } }), BoundOperation(&Operation68, { InputSlice { 0, 16, 24 }, InputSlice { 1, 16, 24 } }), BoundOperation(&Operation68, { InputSlice { 0, 24, 32 }, InputSlice { 1, 24, 32 } }), BoundOperation(&Operation68, { InputSlice { 0, 32, 40 }, InputSlice { 1, 32, 40 } }), BoundOperation(&Operation68, { InputSlice { 0, 40, 48 }, InputSlice { 1, 40, 48 } }), BoundOperation(&Operation68, { InputSlice { 0, 48, 56 }, InputSlice { 1, 48, 56 } }), BoundOperation(&Operation68, { InputSlice { 0, 56, 64 }, InputSlice { 1, 56, 64 } }), BoundOperation(&Operation68, { InputSlice { 0, 64, 72 }, InputSlice { 1, 64, 72 } }), BoundOperation(&Operation68, { InputSlice { 0, 72, 80 }, InputSlice { 1, 72, 80 } }), BoundOperation(&Operation68, { InputSlice { 0, 80, 88 }, InputSlice { 1, 80, 88 } }), BoundOperation(&Operation68, { InputSlice { 0, 88, 96 }, InputSlice { 1, 88, 96 } }), BoundOperation(&Operation68, { InputSlice { 0, 96, 104 }, InputSlice { 1, 96, 104 } }), BoundOperation(&Operation68, { InputSlice { 0, 104, 112 }, InputSlice { 1, 104, 112 } }), BoundOperation(&Operation68, { InputSlice { 0, 112, 120 }, InputSlice { 1, 112, 120 } }), BoundOperation(&Operation68, { InputSlice { 0, 120, 128 }, InputSlice { 1, 120, 128 } }) }, 1),
InstBinding("vsubq_u16", {  }, InstSignature { { 128, 128 }, { 128 }, false }, { BoundOperation(&Operation69, { InputSlice { 0, 0, 16 }, InputSlice { 1, 0, 16 } }), BoundOperation(&Operation69, { InputSlice { 0, 16, 32 }, InputSlice { 1, 16, 32 } }), BoundOperation(&Operation69, { InputSlice { 0, 32, 48 }, InputSlice { 1, 32, 48 } }), BoundOperation(&Operation69, { InputSlice { 0, 48, 64 }, InputSlice { 1, 48, 64 } }), BoundOperation(&Operation69, { InputSlice { 0, 64, 80 }, InputSlice { 1, 64, 80 } }), BoundOperation(&Operation69, { InputSlice { 0, 80, 96 }, InputSlice { 1, 80, 96 } }), BoundOperation(&Operation69, { InputSlice { 0, 96, 112 }, InputSlice { 1, 96, 112 } }), BoundOperation(&Operation69, { InputSlice { 0, 112, 128 }, InputSlice { 1, 112, 128 } }) }, 1),
InstBinding("vsubq_u32", {  }, InstSignature { { 128, 128 }, { 128 }, false }, { BoundOperation(&Operation70, { InputSlice { 0, 0, 32 }, InputSlice { 1, 0, 32 } }), BoundOperation(&Operation70, { InputSlice { 0, 32, 64 }, InputSlice { 1, 32, 64 } }), BoundOperation(&Operation70, { InputSlice { 0, 64, 96 }, InputSlice { 1, 64, 96 } }), BoundOperation(&Operation70, { InputSlice { 0, 96, 128 }, InputSlice { 1, 96, 128 } }) }, 1),
InstBinding("vsubq_u64", {  }, InstSignature { { 128, 128 }, { 128 }, false }, { BoundOperation(&Operation71, { InputSlice { 0, 0, 64 }, InputSlice { 1, 0, 64 } }), BoundOperation(&Operation71, { InputSlice { 0, 64, 128 }, InputSlice { 1, 64, 128 } }) }, 1),
InstBinding("vsubl_s8", {  }, InstSignature { { 64, 64 }, { 128 }, false }, { BoundOperation(&Operation73, { InputSlice { 0, 0, 8 }, InputSlice { 1, 0, 8 } }), BoundOperation(&Operation73, { InputSlice { 0, 8, 16 }, InputSlice { 1, 8, 16 } }), BoundOperation(&Operation73, { InputSlice { 0, 16, 24 }, InputSlice { 1, 16, 24 } }), BoundOperation(&Operation73, { InputSlice { 0, 24, 32 }, InputSlice { 1, 24, 32 } }), BoundOperation(&Operation73, { InputSlice { 0, 32, 40 }, InputSlice { 1, 32, 40 } }), BoundOperation(&Operation73, { InputSlice { 0, 40, 48 }, InputSlice { 1, 40, 48 } }), BoundOperation(&Operation73, { InputSlice { 0, 48, 56 }, InputSlice { 1, 48, 56 } }), BoundOperation(&Operation73, { InputSlice { 0, 56, 64 }, InputSlice { 1, 56, 64 } }) }, 1),
InstBinding("vsubl_s16", {  }, InstSignature { { 64, 64 }, { 128 }, false }, { BoundOperation(&Operation74, { InputSlice { 0, 0, 16 }, InputSlice { 1, 0, 16 } }), BoundOperation(&Operation74, { InputSlice { 0, 16, 32 }, InputSlice { 1, 16, 32 } }), BoundOperation(&Operation74, { InputSlice { 0, 32, 48 }, InputSlice { 1, 32, 48 } }), BoundOperation(&Operation74, { InputSlice { 0, 48, 64 }, InputSlice { 1, 48, 64 } }) }, 1),
InstBinding("vsubl_s32", {  }, InstSignature { { 64, 64 }, { 128 }, false }, { BoundOperation(&Operation75, { InputSlice { 0, 0, 32 }, InputSlice { 1, 0, 32 } }), BoundOperation(&Operation75, { InputSlice { 0, 32, 64 }, InputSlice { 1, 32, 64 } }) }, 1),
InstBinding("vsubl_u8", {  }, InstSignature { { 64, 64 }, { 128 }, false }, { BoundOperation(&Operation76, { InputSlice { 0, 0, 8 }, InputSlice { 1, 0, 8 } }), BoundOperation(&Operation76, { InputSlice { 0, 8, 16 }, InputSlice { 1, 8, 16 } }), BoundOperation(&Operation76, { InputSlice { 0, 16, 24 }, InputSlice { 1, 16, 24 } }), BoundOperation(&Operation76, { InputSlice { 0, 24, 32 }, InputSlice { 1, 24, 32 } }), BoundOperation(&Operation76, { InputSlice { 0, 32, 40 }, InputSlice { 1, 32, 40 } }), BoundOperation(&Operation76, { InputSlice { 0, 40, 48 }, InputSlice { 1, 40, 48 } }), BoundOperation(&Operation76, { InputSlice { 0, 48, 56 }, InputSlice { 1, 48, 56 } }), BoundOperation(&Operation76, { InputSlice { 0, 56, 64 }, InputSlice { 1, 56, 64 } }) }, 1),
InstBinding("vsubl_u16", {  }, InstSignature { { 64, 64 }, { 128 }, false }, { BoundOperation(&Operation77, { InputSlice { 0, 0, 16 }, InputSlice { 1, 0, 16 } }), BoundOperation(&Operation77, { InputSlice { 0, 16, 32 }, InputSlice { 1, 16, 32 } }), BoundOperation(&Operation77, { InputSlice { 0, 32, 48 }, InputSlice { 1, 32, 48 } }), BoundOperation(&Operation77, { InputSlice { 0, 48, 64 }, InputSlice { 1, 48, 64 } }) }, 1),
InstBinding("vsubl_u32", {  }, InstSignature { { 64, 64 }, { 128 }, false }, { BoundOperation(&Operation78, { InputSlice { 0, 0, 32 }, InputSlice { 1, 0, 32 } }), BoundOperation(&Operation78, { InputSlice { 0, 32, 64 }, InputSlice { 1, 32, 64 } }) }, 1),
InstBinding("vsubw_s8", {  }, InstSignature { { 128, 64 }, { 128 }, false }, { BoundOperation(&Operation79, { InputSlice { 0, 0, 16 }, InputSlice { 1, 0, 8 } }), BoundOperation(&Operation79, { InputSlice { 0, 16, 32 }, InputSlice { 1, 8, 16 } }), BoundOperation(&Operation79, { InputSlice { 0, 32, 48 }, InputSlice { 1, 16, 24 } }), BoundOperation(&Operation79, { InputSlice { 0, 48, 64 }, InputSlice { 1, 24, 32 } }), BoundOperation(&Operation79, { InputSlice { 0, 64, 80 }, InputSlice { 1, 32, 40 } }), BoundOperation(&Operation79, { InputSlice { 0, 80, 96 }, InputSlice { 1, 40, 48 } }), BoundOperation(&Operation79, { InputSlice { 0, 96, 112 }, InputSlice { 1, 48, 56 } }), BoundOperation(&Operation79, { InputSlice { 0, 112, 128 }, InputSlice { 1, 56, 64 } }) }, 1),
InstBinding("vsubw_s16", {  }, InstSignature { { 128, 64 }, { 128 }, false }, { BoundOperation(&Operation80, { InputSlice { 0, 0, 32 }, InputSlice { 1, 0, 16 } }), BoundOperation(&Operation80, { InputSlice { 0, 32, 64 }, InputSlice { 1, 16, 32 } }), BoundOperation(&Operation80, { InputSlice { 0, 64, 96 }, InputSlice { 1, 32, 48 } }), BoundOperation(&Operation80, { InputSlice { 0, 96, 128 }, InputSlice { 1, 48, 64 } }) }, 1),
InstBinding("vsubw_s32", {  }, InstSignature { { 128, 64 }, { 128 }, false }, { BoundOperation(&Operation81, { InputSlice { 0, 0, 64 }, InputSlice { 1, 0, 32 } }), BoundOperation(&Operation81, { InputSlice { 0, 64, 128 }, InputSlice { 1, 32, 64 } }) }, 1),
InstBinding("vsubw_u8", {  }, InstSignature { { 128, 64 }, { 128 }, false }, { BoundOperation(&Operation82, { InputSlice { 0, 0, 16 }, InputSlice { 1, 0, 8 } }), BoundOperation(&Operation82, { InputSlice { 0, 16, 32 }, InputSlice { 1, 8, 16 } }), BoundOperation(&Operation82, { InputSlice { 0, 32, 48 }, InputSlice { 1, 16, 24 } }), BoundOperation(&Operation82, { InputSlice { 0, 48, 64 }, InputSlice { 1, 24, 32 } }), BoundOperation(&Operation82, { InputSlice { 0, 64, 80 }, InputSlice { 1, 32, 40 } }), BoundOperation(&Operation82, { InputSlice { 0, 80, 96 }, InputSlice { 1, 40, 48 } }), BoundOperation(&Operation82, { InputSlice { 0, 96, 112 }, InputSlice { 1, 48, 56 } }), BoundOperation(&Operation82, { InputSlice { 0, 112, 128 }, InputSlice { 1, 56, 64 } }) }, 1),
InstBinding("vsubw_u16", {  }, InstSignature { { 128, 64 }, { 128 }, false }, { BoundOperation(&Operation83, { InputSlice { 0, 0, 32 }, InputSlice { 1, 0, 16 } }), BoundOperation(&Operation83, { InputSlice { 0, 32, 64 }, InputSlice { 1, 16, 32 } }), BoundOperation(&Operation83, { InputSlice { 0, 64, 96 }, InputSlice { 1, 32, 48 } }), BoundOperation(&Operation83, { InputSlice { 0, 96, 128 }, InputSlice { 1, 48, 64 } }) }, 1),
InstBinding("vsubw_u32", {  }, InstSignature { { 128, 64 }, { 128 }, false }, { BoundOperation(&Operation84, { InputSlice { 0, 0, 64 }, InputSlice { 1, 0, 32 } }), BoundOperation(&Operation84, { InputSlice { 0, 64, 128 }, InputSlice { 1, 32, 64 } }) }, 1),
InstBinding("vqsub_s8", {  }, InstSignature { { 64, 64 }, { 64 }, false }, { BoundOperation(&Operation85, { InputSlice { 0, 0, 8 }, InputSlice { 1, 0, 8 } }), BoundOperation(&Operation85, { InputSlice { 0, 8, 16 }, InputSlice { 1, 8, 16 } }), BoundOperation(&Operation85, { InputSlice { 0, 16, 24 }, InputSlice { 1, 16, 24 } }), BoundOperation(&Operation85, { InputSlice { 0, 24, 32 }, InputSlice { 1, 24, 32 } }), BoundOperation(&Operation85, { InputSlice { 0, 32, 40 }, InputSlice { 1, 32, 40 } }), BoundOperation(&Operation85, { InputSlice { 0, 40, 48 }, InputSlice { 1, 40, 48 } }), BoundOperation(&Operation85, { InputSlice { 0, 48, 56 }, InputSlice { 1, 48, 56 } }), BoundOperation(&Operation85, { InputSlice { 0, 56, 64 }, InputSlice { 1, 56, 64 } }) }, 1),
InstBinding("vqsub_s16", {  }, InstSignature { { 64, 64 }, { 64 }, false }, { BoundOperation(&Operation86, { InputSlice { 0, 0, 16 }, InputSlice { 1, 0, 16 } }), BoundOperation(&Operation86, { InputSlice { 0, 16, 32 }, InputSlice { 1, 16, 32 } }), BoundOperation(&Operation86, { InputSlice { 0, 32, 48 }, InputSlice { 1, 32, 48 } }), BoundOperation(&Operation86, { InputSlice { 0, 48, 64 }, InputSlice { 1, 48, 64 } }) }, 1),
InstBinding("vqsub_s32", {  }, InstSignature { { 64, 64 }, { 64 }, false }, { BoundOperation(&Operation87, { InputSlice { 0, 0, 32 }, InputSlice { 1, 0, 32 } }), BoundOperation(&Operation87, { InputSlice { 0, 32, 64 }, InputSlice { 1, 32, 64 } }) }, 1),
InstBinding("vqsub_u8", {  }, InstSignature { { 64, 64 }, { 64 }, false }, { BoundOperation(&Operation88, { InputSlice { 0, 0, 8 }, InputSlice { 1, 0, 8 } }), BoundOperation(&Operation88, { InputSlice { 0, 8, 16 }, InputSlice { 1, 8, 16 } }), BoundOperation(&Operation88, { InputSlice { 0, 16, 24 }, InputSlice { 1, 16, 24 } }), BoundOperation(&Operation88, { InputSlice { 0, 24, 32 }, InputSlice { 1, 24, 32 } }), BoundOperation(&Operation88, { InputSlice { 0, 32, 40 }, InputSlice { 1, 32, 40 } }), BoundOperation(&Operation88, { InputSlice { 0, 40, 48 }, InputSlice { 1, 40, 48 } }), BoundOperation(&Operation88, { InputSlice { 0, 48, 56 }, InputSlice { 1, 48, 56 } }), BoundOperation(&Operation88, { InputSlice { 0, 56, 64 }, InputSlice { 1, 56, 64 } }) }, 1),
InstBinding("vqsub_u16", {  }, InstSignature { { 64, 64 }, { 64 }, false }, { BoundOperation(&Operation89, { InputSlice { 0, 0, 16 }, InputSlice { 1, 0, 16 } }), BoundOperation(&Operation89, { InputSlice { 0, 16, 32 }, InputSlice { 1, 16, 32 } }), BoundOperation(&Operation89, { InputSlice { 0, 32, 48 }, InputSlice { 1, 32, 48 } }), BoundOperation(&Operation89, { InputSlice { 0, 48, 64 }, InputSlice { 1, 48, 64 } }) }, 1),
InstBinding("vqsub_u32", {  }, InstSignature { { 64, 64 }, { 64 }, false }, { BoundOperation(&Operation90, { InputSlice { 0, 0, 32 }, InputSlice { 1, 0, 32 } }), BoundOperation(&Operation90, { InputSlice { 0, 32, 64 }, InputSlice { 1, 32, 64 } }) }, 1),
InstBinding("vqsubq_s8", {  }, InstSignature { { 128, 128 }, { 128 }, false }, { BoundOperation(&Operation85, { InputSlice { 0, 0, 8 }, InputSlice { 1, 0, 8 } }), BoundOperation(&Operation85, { InputSlice { 0, 8, 16 }, InputSlice { 1, 8, 16 } }), BoundOperation(&Operation85, { InputSlice { 0, 16, 24 }, InputSlice { 1, 16, 24 } }), BoundOperation(&Operation85, { InputSlice { 0, 24, 32 }, InputSlice { 1, 24, 32 } }), BoundOperation(&Operation85, { InputSlice { 0, 32, 40 }, InputSlice { 1, 32, 40 } }), BoundOperation(&Operation85, { InputSlice { 0, 40, 48 }, InputSlice { 1, 40, 48 } }), BoundOperation(&Operation85, { InputSlice { 0, 48, 56 }, InputSlice { 1, 48, 56 } }), BoundOperation(&Operation85, { InputSlice { 0, 56, 64 }, InputSlice { 1, 56, 64 } }), BoundOperation(&Operation85, { InputSlice { 0, 64, 72 }, InputSlice { 1, 64, 72 } }), BoundOperation(&Operation85, { InputSlice { 0, 72, 80 }, InputSlice { 1, 72, 80 } }), BoundOperation(&Operation85, { InputSlice { 0, 80, 88 }, InputSlice { 1, 80, 88 } }), BoundOperation(&Operation85, { InputSlice { 0, 88, 96 }, InputSlice { 1, 88, 96 } }), BoundOperation(&Operation85, { InputSlice { 0, 96, 104 }, InputSlice { 1, 96, 104 } }), BoundOperation(&Operation85, { InputSlice { 0, 104, 112 }, InputSlice { 1, 104, 112 } }), BoundOperation(&Operation85, { InputSlice { 0, 112, 120 }, InputSlice { 1, 112, 120 } }), BoundOperation(&Operation85, { InputSlice { 0, 120, 128 }, InputSlice { 1, 120, 128 } }) }, 1),
InstBinding("vqsubq_s16", {  }, InstSignature { { 128, 128 }, { 128 }, false }, { BoundOperation(&Operation86, { InputSlice { 0, 0, 16 }, InputSlice { 1, 0, 16 } }), BoundOperation(&Operation86, { InputSlice { 0, 16, 32 }, InputSlice { 1, 16, 32 } }), BoundOperation(&Operation86, { InputSlice { 0, 32, 48 }, InputSlice { 1, 32, 48 } }), BoundOperation(&Operation86, { InputSlice { 0, 48, 64 }, InputSlice { 1, 48, 64 } }), BoundOperation(&Operation86, { InputSlice { 0, 64, 80 }, InputSlice { 1, 64, 80 } }), BoundOperation(&Operation86, { InputSlice { 0, 80, 96 }, InputSlice { 1, 80, 96 } }), BoundOperation(&Operation86, { InputSlice { 0, 96, 112 }, InputSlice { 1, 96, 112 } }), BoundOperation(&Operation86, { InputSlice { 0, 112, 128 }, InputSlice { 1, 112, 128 } }) }, 1),
InstBinding("vqsubq_s32", {  }, InstSignature { { 128, 128 }, { 128 }, false }, { BoundOperation(&Operation87, { InputSlice { 0, 0, 32 }, InputSlice { 1, 0, 32 } }), BoundOperation(&Operation87, { InputSlice { 0, 32, 64 }, InputSlice { 1, 32, 64 } }), BoundOperation(&Operation87, { InputSlice { 0, 64, 96 }, InputSlice { 1, 64, 96 } }), BoundOperation(&Operation87, { InputSlice { 0, 96, 128 }, InputSlice { 1, 96, 128 } }) }, 1),
InstBinding("vqsubq_u8", {  }, InstSignature { { 128, 128 }, { 128 }, false }, { BoundOperation(&Operation88, { InputSlice { 0, 0, 8 }, InputSlice { 1, 0, 8 } }), BoundOperation(&Operation88, { InputSlice { 0, 8, 16 }, InputSlice { 1, 8, 16 } }), BoundOperation(&Operation88, { InputSlice { 0, 16, 24 }, InputSlice { 1, 16, 24 } }), BoundOperation(&Operation88, { InputSlice { 0, 24, 32 }, InputSlice { 1, 24, 32 } }), BoundOperation(&Operation88, { InputSlice { 0, 32, 40 }, InputSlice { 1, 32, 40 } }), BoundOperation(&Operation88, { InputSlice { 0, 40, 48 }, InputSlice { 1, 40, 48 } }), BoundOperation(&Operation88, { InputSlice { 0, 48, 56 }, InputSlice { 1, 48, 56 } }), BoundOperation(&Operation88, { InputSlice { 0, 56, 64 }, InputSlice { 1, 56, 64 } }), BoundOperation(&Operation88, { InputSlice { 0, 64, 72 }, InputSlice { 1, 64, 72 } }), BoundOperation(&Operation88, { InputSlice { 0, 72, 80 }, InputSlice { 1, 72, 80 } }), BoundOperation(&Operation88, { InputSlice { 0, 80, 88 }, InputSlice { 1, 80, 88 } }), BoundOperation(&Operation88, { InputSlice { 0, 88, 96 }, InputSlice { 1, 88, 96 } }), BoundOperation(&Operation88, { InputSlice { 0, 96, 104 }, InputSlice { 1, 96, 104 } }), BoundOperation(&Operation88, { InputSlice { 0, 104, 112 }, InputSlice { 1, 104, 112 } }), BoundOperation(&Operation88, { InputSlice { 0, 112, 120 }, InputSlice { 1, 112, 120 } }), BoundOperation(&Operation88, { InputSlice { 0, 120, 128 }, InputSlice { 1, 120, 128 } }) }, 1),
InstBinding("vqsubq_u16", {  }, InstSignature { { 128, 128 }, { 128 }, false }, { BoundOperation(&Operation89, { InputSlice { 0, 0, 16 }, InputSlice { 1, 0, 16 } }), BoundOperation(&Operation89, { InputSlice { 0, 16, 32 }, InputSlice { 1, 16, 32 } }), BoundOperation(&Operation89, { InputSlice { 0, 32, 48 }, InputSlice { 1, 32, 48 } }), BoundOperation(&Operation89, { InputSlice { 0, 48, 64 }, InputSlice { 1, 48, 64 } }), BoundOperation(&Operation89, { InputSlice { 0, 64, 80 }, InputSlice { 1, 64, 80 } }), BoundOperation(&Operation89, { InputSlice { 0, 80, 96 }, InputSlice { 1, 80, 96 } }), BoundOperation(&Operation89, { InputSlice { 0, 96, 112 }, InputSlice { 1, 96, 112 } }), BoundOperation(&Operation89, { InputSlice { 0, 112, 128 }, InputSlice { 1, 112, 128 } }) }, 1),
InstBinding("vqsubq_u32", {  }, InstSignature { { 128, 128 }, { 128 }, false }, { BoundOperation(&Operation90, { InputSlice { 0, 0, 32 }, InputSlice { 1, 0, 32 } }), BoundOperation(&Operation90, { InputSlice { 0, 32, 64 }, InputSlice { 1, 32, 64 } }), BoundOperation(&Operation90, { InputSlice { 0, 64, 96 }, InputSlice { 1, 64, 96 } }), BoundOperation(&Operation90, { InputSlice { 0, 96, 128 }, InputSlice { 1, 96, 128 } }) }, 1),
InstBinding("vhsub_s8", {  }, InstSignature { { 64, 64 }, { 64 }, false }, { BoundOperation(&Operation91, { InputSlice { 0, 0, 8 }, InputSlice { 1, 0, 8 } }), BoundOperation(&Operation91, { InputSlice { 0, 8, 16 }, InputSlice { 1, 8, 16 } }), BoundOperation(&Operation91, { InputSlice { 0, 16, 24 }, InputSlice { 1, 16, 24 } }), BoundOperation(&Operation91, { InputSlice { 0, 24, 32 }, InputSlice { 1, 24, 32 } }), BoundOperation(&Operation91, { InputSlice { 0, 32, 40 }, InputSlice { 1, 32, 40 } }), BoundOperation(&Operation91, { InputSlice { 0, 40, 48 }, InputSlice { 1, 40, 48 } }), BoundOperation(&Operation91, { InputSlice { 0, 48, 56 }, InputSlice { 1, 48, 56 } }), BoundOperation(&Operation91, { InputSlice { 0, 56, 64 }, InputSlice { 1, 56, 64 } }) }, 1),
InstBinding("vhsub_s16", {  }, InstSignature { { 64, 64 }, { 64 }, false }, { BoundOperation(&Operation92, { InputSlice { 0, 0, 16 }, InputSlice { 1, 0, 16 } }), BoundOperation(&Operation92, { InputSlice { 0, 16, 32 }, InputSlice { 1, 16, 32 } }), BoundOperation(&Operation92, { InputSlice { 0, 32, 48 }, InputSlice { 1, 32, 48 } }), BoundOperation(&Operation92, { InputSlice { 0, 48, 64 }, InputSlice { 1, 48, 64 } }) }, 1),
InstBinding("vhsub_s32", {  }, InstSignature { { 64, 64 }, { 64 }, false }, { BoundOperation(&Operation93, { InputSlice { 0, 0, 32 }, InputSlice { 1, 0, 32 } }), BoundOperation(&Operation93, { InputSlice { 0, 32, 64 }, InputSlice { 1, 32, 64 } }) }, 1),
InstBinding("vhsub_u8", {  }, InstSignature { { 64, 64 }, { 64 }, false }, { BoundOperation(&Operation94, { InputSlice { 0, 0, 8 }, InputSlice { 1, 0, 8 } }), BoundOperation(&Operation94, { InputSlice { 0, 8, 16 }, InputSlice { 1, 8, 16 } }), BoundOperation(&Operation94, { InputSlice { 0, 16, 24 }, InputSlice { 1, 16, 24 } }), BoundOperation(&Operation94, { InputSlice { 0, 24, 32 }, InputSlice { 1, 24, 32 } }), BoundOperation(&Operation94, { InputSlice { 0, 32, 40 }, InputSlice { 1, 32, 40 } }), BoundOperation(&Operation94, { InputSlice { 0, 40, 48 }, InputSlice { 1, 40, 48 } }), BoundOperation(&Operation94, { InputSlice { 0, 48, 56 }, InputSlice { 1, 48, 56 } }), BoundOperation(&Operation94, { InputSlice { 0, 56, 64 }, InputSlice { 1, 56, 64 } }) }, 1),
InstBinding("vhsub_u16", {  }, InstSignature { { 64, 64 }, { 64 }, false }, { BoundOperation(&Operation95, { InputSlice { 0, 0, 16 }, InputSlice { 1, 0, 16 } }), BoundOperation(&Operation95, { InputSlice { 0, 16, 32 }, InputSlice { 1, 16, 32 } }), BoundOperation(&Operation95, { InputSlice { 0, 32, 48 }, InputSlice { 1, 32, 48 } }), BoundOperation(&Operation95, { InputSlice { 0, 48, 64 }, InputSlice { 1, 48, 64 } }) }, 1),
InstBinding("vhsub_u32", {  }, InstSignature { { 64, 64 }, { 64 }, false }, { BoundOperation(&Operation96, { InputSlice { 0, 0, 32 }, InputSlice { 1, 0, 32 } }), BoundOperation(&Operation96, { InputSlice { 0, 32, 64 }, InputSlice { 1, 32, 64 } }) }, 1),
InstBinding("vhsubq_s8", {  }, InstSignature { { 128, 128 }, { 128 }, false }, { BoundOperation(&Operation91, { InputSlice { 0, 0, 8 }, InputSlice { 1, 0, 8 } }), BoundOperation(&Operation91, { InputSlice { 0, 8, 16 }, InputSlice { 1, 8, 16 } }), BoundOperation(&Operation91, { InputSlice { 0, 16, 24 }, InputSlice { 1, 16, 24 } }), BoundOperation(&Operation91, { InputSlice { 0, 24, 32 }, InputSlice { 1, 24, 32 } }), BoundOperation(&Operation91, { InputSlice { 0, 32, 40 }, InputSlice { 1, 32, 40 } }), BoundOperation(&Operation91, { InputSlice { 0, 40, 48 }, InputSlice { 1, 40, 48 } }), BoundOperation(&Operation91, { InputSlice { 0, 48, 56 }, InputSlice { 1, 48, 56 } }), BoundOperation(&Operation91, { InputSlice { 0, 56, 64 }, InputSlice { 1, 56, 64 } }), BoundOperation(&Operation91, { InputSlice { 0, 64, 72 }, InputSlice { 1, 64, 72 } }), BoundOperation(&Operation91, { InputSlice { 0, 72, 80 }, InputSlice { 1, 72, 80 } }), BoundOperation(&Operation91, { InputSlice { 0, 80, 88 }, InputSlice { 1, 80, 88 } }), BoundOperation(&Operation91, { InputSlice { 0, 88, 96 }, InputSlice { 1, 88, 96 } }), BoundOperation(&Operation91, { InputSlice { 0, 96, 104 }, InputSlice { 1, 96, 104 } }), BoundOperation(&Operation91, { InputSlice { 0, 104, 112 }, InputSlice { 1, 104, 112 } }), BoundOperation(&Operation91, { InputSlice { 0, 112, 120 }, InputSlice { 1, 112, 120 } }), BoundOperation(&Operation91, { InputSlice { 0, 120, 128 }, InputSlice { 1, 120, 128 } }) }, 1),
InstBinding("vhsubq_s16", {  }, InstSignature { { 128, 128 }, { 128 }, false }, { BoundOperation(&Operation92, { InputSlice { 0, 0, 16 }, InputSlice { 1, 0, 16 } }), BoundOperation(&Operation92, { InputSlice { 0, 16, 32 }, InputSlice { 1, 16, 32 } }), BoundOperation(&Operation92, { InputSlice { 0, 32, 48 }, InputSlice { 1, 32, 48 } }), BoundOperation(&Operation92, { InputSlice { 0, 48, 64 }, InputSlice { 1, 48, 64 } }), BoundOperation(&Operation92, { InputSlice { 0, 64, 80 }, InputSlice { 1, 64, 80 } }), BoundOperation(&Operation92, { InputSlice { 0, 80, 96 }, InputSlice { 1, 80, 96 } }), BoundOperation(&Operation92, { InputSlice { 0, 96, 112 }, InputSlice { 1, 96, 112 } }), BoundOperation(&Operation92, { InputSlice { 0, 112, 128 }, InputSlice { 1, 112, 128 } }) }, 1),
InstBinding("vhsubq_s32", {  }, InstSignature { { 128, 128 }, { 128 }, false }, { BoundOperation(&Operation93, { InputSlice { 0, 0, 32 }, InputSlice { 1, 0, 32 } }), BoundOperation(&Operation93, { InputSlice { 0, 32, 64 }, InputSlice { 1, 32, 64 } }), BoundOperation(&Operation93, { InputSlice { 0, 64, 96 }, InputSlice { 1, 64, 96 } }), BoundOperation(&Operation93, { InputSlice { 0, 96, 128 }, InputSlice { 1, 96, 128 } }) }, 1),
InstBinding("vhsubq_u8", {  }, InstSignature { { 128, 128 }, { 128 }, false }, { BoundOperation(&Operation94, { InputSlice { 0, 0, 8 }, InputSlice { 1, 0, 8 } }), BoundOperation(&Operation94, { InputSlice { 0, 8, 16 }, InputSlice { 1, 8, 16 } }), BoundOperation(&Operation94, { InputSlice { 0, 16, 24 }, InputSlice { 1, 16, 24 } }), BoundOperation(&Operation94, { InputSlice { 0, 24, 32 }, InputSlice { 1, 24, 32 } }), BoundOperation(&Operation94, { InputSlice { 0, 32, 40 }, InputSlice { 1, 32, 40 } }), BoundOperation(&Operation94, { InputSlice { 0, 40, 48 }, InputSlice { 1, 40, 48 } }), BoundOperation(&Operation94, { InputSlice { 0, 48, 56 }, InputSlice { 1, 48, 56 } }), BoundOperation(&Operation94, { InputSlice { 0, 56, 64 }, InputSlice { 1, 56, 64 } }), BoundOperation(&Operation94, { InputSlice { 0, 64, 72 }, InputSlice { 1, 64, 72 } }), BoundOperation(&Operation94, { InputSlice { 0, 72, 80 }, InputSlice { 1, 72, 80 } }), BoundOperation(&Operation94, { InputSlice { 0, 80, 88 }, InputSlice { 1, 80, 88 } }), BoundOperation(&Operation94, { InputSlice { 0, 88, 96 }, InputSlice { 1, 88, 96 } }), BoundOperation(&Operation94, { InputSlice { 0, 96, 104 }, InputSlice { 1, 96, 104 } }), BoundOperation(&Operation94, { InputSlice { 0, 104, 112 }, InputSlice { 1, 104, 112 } }), BoundOperation(&Operation94, { InputSlice { 0, 112, 120 }, InputSlice { 1, 112, 120 } }), BoundOperation(&Operation94, { InputSlice { 0, 120, 128 }, InputSlice { 1, 120, 128 } }) }, 1),
InstBinding("vhsubq_u16", {  }, InstSignature { { 128, 128 }, { 128 }, false }, { BoundOperation(&Operation95, { InputSlice { 0, 0, 16 }, InputSlice { 1, 0, 16 } }), BoundOperation(&Operation95, { InputSlice { 0, 16, 32 }, InputSlice { 1, 16, 32 } }), BoundOperation(&Operation95, { InputSlice { 0, 32, 48 }, InputSlice { 1, 32, 48 } }), BoundOperation(&Operation95, { InputSlice { 0, 48, 64 }, InputSlice { 1, 48, 64 } }), BoundOperation(&Operation95, { InputSlice { 0, 64, 80 }, InputSlice { 1, 64, 80 } }), BoundOperation(&Operation95, { InputSlice { 0, 80, 96 }, InputSlice { 1, 80, 96 } }), BoundOperation(&Operation95, { InputSlice { 0, 96, 112 }, InputSlice { 1, 96, 112 } }), BoundOperation(&Operation95, { InputSlice { 0, 112, 128 }, InputSlice { 1, 112, 128 } }) }, 1),
InstBinding("vhsubq_u32", {  }, InstSignature { { 128, 128 }, { 128 }, false }, { BoundOperation(&Operation96, { InputSlice { 0, 0, 32 }, InputSlice { 1, 0, 32 } }), BoundOperation(&Operation96, { InputSlice { 0, 32, 64 }, InputSlice { 1, 32, 64 } }), BoundOperation(&Operation96, { InputSlice { 0, 64, 96 }, InputSlice { 1, 64, 96 } }), BoundOperation(&Operation96, { InputSlice { 0, 96, 128 }, InputSlice { 1, 96, 128 } }) }, 1),
InstBinding("vsubhn_s16", {  }, InstSignature { { 128, 128 }, { 64 }, false }, { BoundOperation(&Operation97, { InputSlice { 0, 0, 16 }, InputSlice { 1, 0, 16 } }), BoundOperation(&Operation97, { InputSlice { 0, 16, 32 }, InputSlice { 1, 16, 32 } }), BoundOperation(&Operation97, { InputSlice { 0, 32, 48 }, InputSlice { 1, 32, 48 } }), BoundOperation(&Operation97, { InputSlice { 0, 48, 64 }, InputSlice { 1, 48, 64 } }), BoundOperation(&Operation97, { InputSlice { 0, 64, 80 }, InputSlice { 1, 64, 80 } }), BoundOperation(&Operation97, { InputSlice { 0, 80, 96 }, InputSlice { 1, 80, 96 } }), BoundOperation(&Operation97, { InputSlice { 0, 96, 112 }, InputSlice { 1, 96, 112 } }), BoundOperation(&Operation97, { InputSlice { 0, 112, 128 }, InputSlice { 1, 112, 128 } }) }, 1),
InstBinding("vsubhn_s32", {  }, InstSignature { { 128, 128 }, { 64 }, false }, { BoundOperation(&Operation98, { InputSlice { 0, 0, 32 }, InputSlice { 1, 0, 32 } }), BoundOperation(&Operation98, { InputSlice { 0, 32, 64 }, InputSlice { 1, 32, 64 } }), BoundOperation(&Operation98, { InputSlice { 0, 64, 96 }, InputSlice { 1, 64, 96 } }), BoundOperation(&Operation98, { InputSlice { 0, 96, 128 }, InputSlice { 1, 96, 128 } }) }, 1),
InstBinding("vsubhn_u16", {  }, InstSignature { { 128, 128 }, { 64 }, false }, { BoundOperation(&Operation97, { InputSlice { 0, 0, 16 }, InputSlice { 1, 0, 16 } }), BoundOperation(&Operation97, { InputSlice { 0, 16, 32 }, InputSlice { 1, 16, 32 } }), BoundOperation(&Operation97, { InputSlice { 0, 32, 48 }, InputSlice { 1, 32, 48 } }), BoundOperation(&Operation97, { InputSlice { 0, 48, 64 }, InputSlice { 1, 48, 64 } }), BoundOperation(&Operation97, { InputSlice { 0, 64, 80 }, InputSlice { 1, 64, 80 } }), BoundOperation(&Operation97, { InputSlice { 0, 80, 96 }, InputSlice { 1, 80, 96 } }), BoundOperation(&Operation97, { InputSlice { 0, 96, 112 }, InputSlice { 1, 96, 112 } }), BoundOperation(&Operation97, { InputSlice { 0, 112, 128 }, InputSlice { 1, 112, 128 } }) }, 1),
InstBinding("vsubhn_u32", {  }, InstSignature { { 128, 128 }, { 64 }, false }, { BoundOperation(&Operation98, { InputSlice { 0, 0, 32 }, InputSlice { 1, 0, 32 } }), BoundOperation(&Operation98, { InputSlice { 0, 32, 64 }, InputSlice { 1, 32, 64 } }), BoundOperation(&Operation98, { InputSlice { 0, 64, 96 }, InputSlice { 1, 64, 96 } }), BoundOperation(&Operation98, { InputSlice { 0, 96, 128 }, InputSlice { 1, 96, 128 } }) }, 1),
InstBinding("vrsubhn_s16", {  }, InstSignature { { 128, 128 }, { 64 }, false }, { BoundOperation(&Operation99, { InputSlice { 0, 0, 16 }, InputSlice { 1, 0, 16 } }), BoundOperation(&Operation99, { InputSlice { 0, 16, 32 }, InputSlice { 1, 16, 32 } }), BoundOperation(&Operation99, { InputSlice { 0, 32, 48 }, InputSlice { 1, 32, 48 } }), BoundOperation(&Operation99, { InputSlice { 0, 48, 64 }, InputSlice { 1, 48, 64 } }), BoundOperation(&Operation99, { InputSlice { 0, 64, 80 }, InputSlice { 1, 64, 80 } }), BoundOperation(&Operation99, { InputSlice { 0, 80, 96 }, InputSlice { 1, 80, 96 } }), BoundOperation(&Operation99, { InputSlice { 0, 96, 112 }, InputSlice { 1, 96, 112 } }), BoundOperation(&Operation99, { InputSlice { 0, 112, 128 }, InputSlice { 1, 112, 128 } }) }, 1),
InstBinding("vrsubhn_s32", {  }, InstSignature { { 128, 128 }, { 64 }, false }, { BoundOperation(&Operation100, { InputSlice { 0, 0, 32 }, InputSlice { 1, 0, 32 } }), BoundOperation(&Operation100, { InputSlice { 0, 32, 64 }, InputSlice { 1, 32, 64 } }), BoundOperation(&Operation100, { InputSlice { 0, 64, 96 }, InputSlice { 1, 64, 96 } }), BoundOperation(&Operation100, { InputSlice { 0, 96, 128 }, InputSlice { 1, 96, 128 } }) }, 1),
InstBinding("vrsubhn_u16", {  }, InstSignature { { 128, 128 }, { 64 }, false }, { BoundOperation(&Operation99, { InputSlice { 0, 0, 16 }, InputSlice { 1, 0, 16 } }), BoundOperation(&Operation99, { InputSlice { 0, 16, 32 }, InputSlice { 1, 16, 32 } }), BoundOperation(&Operation99, { InputSlice { 0, 32, 48 }, InputSlice { 1, 32, 48 } }), BoundOperation(&Operation99, { InputSlice { 0, 48, 64 }, InputSlice { 1, 48, 64 } }), BoundOperation(&Operation99, { InputSlice { 0, 64, 80 }, InputSlice { 1, 64, 80 } }), BoundOperation(&Operation99, { InputSlice { 0, 80, 96 }, InputSlice { 1, 80, 96 } }), BoundOperation(&Operation99, { InputSlice { 0, 96, 112 }, InputSlice { 1, 96, 112 } }), BoundOperation(&Operation99, { InputSlice { 0, 112, 128 }, InputSlice { 1, 112, 128 } }) }, 1),
InstBinding("vrsubhn_u32", {  }, InstSignature { { 128, 128 }, { 64 }, false }, { BoundOperation(&Operation100, { InputSlice { 0, 0, 32 }, InputSlice { 1, 0, 32 } }), BoundOperation(&Operation100, { InputSlice { 0, 32, 64 }, InputSlice { 1, 32, 64 } }), BoundOperation(&Operation100, { InputSlice { 0, 64, 96 }, InputSlice { 1, 64, 96 } }), BoundOperation(&Operation100, { InputSlice { 0, 96, 128 }, InputSlice { 1, 96, 128 } }) }, 1),
InstBinding("vabd_s8", {  }, InstSignature { { 64, 64 }, { 64 }, false }, { BoundOperation(&Operation101, { InputSlice { 1, 0, 8 }, InputSlice { 0, 0, 8 } }), BoundOperation(&Operation101, { InputSlice { 1, 8, 16 }, InputSlice { 0, 8, 16 } }), BoundOperation(&Operation101, { InputSlice { 1, 16, 24 }, InputSlice { 0, 16, 24 } }), BoundOperation(&Operation101, { InputSlice { 1, 24, 32 }, InputSlice { 0, 24, 32 } }), BoundOperation(&Operation101, { InputSlice { 1, 32, 40 }, InputSlice { 0, 32, 40 } }), BoundOperation(&Operation101, { InputSlice { 1, 40, 48 }, InputSlice { 0, 40, 48 } }), BoundOperation(&Operation101, { InputSlice { 1, 48, 56 }, InputSlice { 0, 48, 56 } }), BoundOperation(&Operation101, { InputSlice { 1, 56, 64 }, InputSlice { 0, 56, 64 } }) }, 1),
InstBinding("vabd_s16", {  }, InstSignature { { 64, 64 }, { 64 }, false }, { BoundOperation(&Operation102, { InputSlice { 1, 0, 16 }, InputSlice { 0, 0, 16 } }), BoundOperation(&Operation102, { InputSlice { 1, 16, 32 }, InputSlice { 0, 16, 32 } }), BoundOperation(&Operation102, { InputSlice { 1, 32, 48 }, InputSlice { 0, 32, 48 } }), BoundOperation(&Operation102, { InputSlice { 1, 48, 64 }, InputSlice { 0, 48, 64 } }) }, 1),
InstBinding("vabd_s32", {  }, InstSignature { { 64, 64 }, { 64 }, false }, { BoundOperation(&Operation103, { InputSlice { 1, 0, 32 }, InputSlice { 0, 0, 32 } }), BoundOperation(&Operation103, { InputSlice { 1, 32, 64 }, InputSlice { 0, 32, 64 } }) }, 1),
InstBinding("vabd_u8", {  }, InstSignature { { 64, 64 }, { 64 }, false }, { BoundOperation(&Operation104, { InputSlice { 1, 0, 8 }, InputSlice { 0, 0, 8 } }), BoundOperation(&Operation104, { InputSlice { 1, 8, 16 }, InputSlice { 0, 8, 16 } }), BoundOperation(&Operation104, { InputSlice { 1, 16, 24 }, InputSlice { 0, 16, 24 } }), BoundOperation(&Operation104, { InputSlice { 1, 24, 32 }, InputSlice { 0, 24, 32 } }), BoundOperation(&Operation104, { InputSlice { 1, 32, 40 }, InputSlice { 0, 32, 40 } }), BoundOperation(&Operation104, { InputSlice { 1, 40, 48 }, InputSlice { 0, 40, 48 } }), BoundOperation(&Operation104, { InputSlice { 1, 48, 56 }, InputSlice { 0, 48, 56 } }), BoundOperation(&Operation104, { InputSlice { 1, 56, 64 }, InputSlice { 0, 56, 64 } }) }, 1),
InstBinding("vabd_u16", {  }, InstSignature { { 64, 64 }, { 64 }, false }, { BoundOperation(&Operation105, { InputSlice { 1, 0, 16 }, InputSlice { 0, 0, 16 } }), BoundOperation(&Operation105, { InputSlice { 1, 16, 32 }, InputSlice { 0, 16, 32 } }), BoundOperation(&Operation105, { InputSlice { 1, 32, 48 }, InputSlice { 0, 32, 48 } }), BoundOperation(&Operation105, { InputSlice { 1, 48, 64 }, InputSlice { 0, 48, 64 } }) }, 1),
InstBinding("vabd_u32", {  }, InstSignature { { 64, 64 }, { 64 }, false }, { BoundOperation(&Operation106, { InputSlice { 1, 0, 32 }, InputSlice { 0, 0, 32 } }), BoundOperation(&Operation106, { InputSlice { 1, 32, 64 }, InputSlice { 0, 32, 64 } }) }, 1),
InstBinding("vabd_f32", {  }, InstSignature { { 64, 64 }, { 64 }, false }, { BoundOperation(&Operation107, { InputSlice { 0, 0, 32 }, InputSlice { 1, 0, 32 } }), BoundOperation(&Operation107, { InputSlice { 0, 32, 64 }, InputSlice { 1, 32, 64 } }) }, 1),
InstBinding("vabdq_s8", {  }, InstSignature { { 128, 128 }, { 128 }, false }, { BoundOperation(&Operation101, { InputSlice { 1, 0, 8 }, InputSlice { 0, 0, 8 } }), BoundOperation(&Operation101, { InputSlice { 1, 8, 16 }, InputSlice { 0, 8, 16 } }), BoundOperation(&Operation101, { InputSlice { 1, 16, 24 }, InputSlice { 0, 16, 24 } }), BoundOperation(&Operation101, { InputSlice { 1, 24, 32 }, InputSlice { 0, 24, 32 } }), BoundOperation(&Operation101, { InputSlice { 1, 32, 40 }, InputSlice { 0, 32, 40 } }), BoundOperation(&Operation101, { InputSlice { 1, 40, 48 }, InputSlice { 0, 40, 48 } }), BoundOperation(&Operation101, { InputSlice { 1, 48, 56 }, InputSlice { 0, 48, 56 } }), BoundOperation(&Operation101, { InputSlice { 1, 56, 64 }, InputSlice { 0, 56, 64 } }), BoundOperation(&Operation101, { InputSlice { 1, 64, 72 }, InputSlice { 0, 64, 72 } }), BoundOperation(&Operation101, { InputSlice { 1, 72, 80 }, InputSlice { 0, 72, 80 } }), BoundOperation(&Operation101, { InputSlice { 1, 80, 88 }, InputSlice { 0, 80, 88 } }), BoundOperation(&Operation101, { InputSlice { 1, 88, 96 }, InputSlice { 0, 88, 96 } }), BoundOperation(&Operation101, { InputSlice { 1, 96, 104 }, InputSlice { 0, 96, 104 } }), BoundOperation(&Operation101, { InputSlice { 1, 104, 112 }, InputSlice { 0, 104, 112 } }), BoundOperation(&Operation101, { InputSlice { 1, 112, 120 }, InputSlice { 0, 112, 120 } }), BoundOperation(&Operation101, { InputSlice { 1, 120, 128 }, InputSlice { 0, 120, 128 } }) }, 1),
InstBinding("vabdq_s16", {  }, InstSignature { { 128, 128 }, { 128 }, false }, { BoundOperation(&Operation102, { InputSlice { 1, 0, 16 }, InputSlice { 0, 0, 16 } }), BoundOperation(&Operation102, { InputSlice { 1, 16, 32 }, InputSlice { 0, 16, 32 } }), BoundOperation(&Operation102, { InputSlice { 1, 32, 48 }, InputSlice { 0, 32, 48 } }), BoundOperation(&Operation102, { InputSlice { 1, 48, 64 }, InputSlice { 0, 48, 64 } }), BoundOperation(&Operation102, { InputSlice { 1, 64, 80 }, InputSlice { 0, 64, 80 } }), BoundOperation(&Operation102, { InputSlice { 1, 80, 96 }, InputSlice { 0, 80, 96 } }), BoundOperation(&Operation102, { InputSlice { 1, 96, 112 }, InputSlice { 0, 96, 112 } }), BoundOperation(&Operation102, { InputSlice { 1, 112, 128 }, InputSlice { 0, 112, 128 } }) }, 1),
InstBinding("vabdq_s32", {  }, InstSignature { { 128, 128 }, { 128 }, false }, { BoundOperation(&Operation103, { InputSlice { 1, 0, 32 }, InputSlice { 0, 0, 32 } }), BoundOperation(&Operation103, { InputSlice { 1, 32, 64 }, InputSlice { 0, 32, 64 } }), BoundOperation(&Operation103, { InputSlice { 1, 64, 96 }, InputSlice { 0, 64, 96 } }), BoundOperation(&Operation103, { InputSlice { 1, 96, 128 }, InputSlice { 0, 96, 128 } }) }, 1),
InstBinding("vabdq_u8", {  }, InstSignature { { 128, 128 }, { 128 }, false }, { BoundOperation(&Operation104, { InputSlice { 1, 0, 8 }, InputSlice { 0, 0, 8 } }), BoundOperation(&Operation104, { InputSlice { 1, 8, 16 }, InputSlice { 0, 8, 16 } }), BoundOperation(&Operation104, { InputSlice { 1, 16, 24 }, InputSlice { 0, 16, 24 } }), BoundOperation(&Operation104, { InputSlice { 1, 24, 32 }, InputSlice { 0, 24, 32 } }), BoundOperation(&Operation104, { InputSlice { 1, 32, 40 }, InputSlice { 0, 32, 40 } }), BoundOperation(&Operation104, { InputSlice { 1, 40, 48 }, InputSlice { 0, 40, 48 } }), BoundOperation(&Operation104, { InputSlice { 1, 48, 56 }, InputSlice { 0, 48, 56 } }), BoundOperation(&Operation104, { InputSlice { 1, 56, 64 }, InputSlice { 0, 56, 64 } }), BoundOperation(&Operation104, { InputSlice { 1, 64, 72 }, InputSlice { 0, 64, 72 } }), BoundOperation(&Operation104, { InputSlice { 1, 72, 80 }, InputSlice { 0, 72, 80 } }), BoundOperation(&Operation104, { InputSlice { 1, 80, 88 }, InputSlice { 0, 80, 88 } }), BoundOperation(&Operation104, { InputSlice { 1, 88, 96 }, InputSlice { 0, 88, 96 } }), BoundOperation(&Operation104, { InputSlice { 1, 96, 104 }, InputSlice { 0, 96, 104 } }), BoundOperation(&Operation104, { InputSlice { 1, 104, 112 }, InputSlice { 0, 104, 112 } }), BoundOperation(&Operation104, { InputSlice { 1, 112, 120 }, InputSlice { 0, 112, 120 } }), BoundOperation(&Operation104, { InputSlice { 1, 120, 128 }, InputSlice { 0, 120, 128 } }) }, 1),
InstBinding("vabdq_u16", {  }, InstSignature { { 128, 128 }, { 128 }, false }, { BoundOperation(&Operation105, { InputSlice { 1, 0, 16 }, InputSlice { 0, 0, 16 } }), BoundOperation(&Operation105, { InputSlice { 1, 16, 32 }, InputSlice { 0, 16, 32 } }), BoundOperation(&Operation105, { InputSlice { 1, 32, 48 }, InputSlice { 0, 32, 48 } }), BoundOperation(&Operation105, { InputSlice { 1, 48, 64 }, InputSlice { 0, 48, 64 } }), BoundOperation(&Operation105, { InputSlice { 1, 64, 80 }, InputSlice { 0, 64, 80 } }), BoundOperation(&Operation105, { InputSlice { 1, 80, 96 }, InputSlice { 0, 80, 96 } }), BoundOperation(&Operation105, { InputSlice { 1, 96, 112 }, InputSlice { 0, 96, 112 } }), BoundOperation(&Operation105, { InputSlice { 1, 112, 128 }, InputSlice { 0, 112, 128 } }) }, 1),
InstBinding("vabdq_u32", {  }, InstSignature { { 128, 128 }, { 128 }, false }, { BoundOperation(&Operation106, { InputSlice { 1, 0, 32 }, InputSlice { 0, 0, 32 } }), BoundOperation(&Operation106, { InputSlice { 1, 32, 64 }, InputSlice { 0, 32, 64 } }), BoundOperation(&Operation106, { InputSlice { 1, 64, 96 }, InputSlice { 0, 64, 96 } }), BoundOperation(&Operation106, { InputSlice { 1, 96, 128 }, InputSlice { 0, 96, 128 } }) }, 1),
InstBinding("vabdq_f32", {  }, InstSignature { { 128, 128 }, { 128 }, false }, { BoundOperation(&Operation107, { InputSlice { 0, 0, 32 }, InputSlice { 1, 0, 32 } }), BoundOperation(&Operation107, { InputSlice { 0, 32, 64 }, InputSlice { 1, 32, 64 } }), BoundOperation(&Operation107, { InputSlice { 0, 64, 96 }, InputSlice { 1, 64, 96 } }), BoundOperation(&Operation107, { InputSlice { 0, 96, 128 }, InputSlice { 1, 96, 128 } }) }, 1),
InstBinding("vabdl_s8", {  }, InstSignature { { 64, 64 }, { 128 }, false }, { BoundOperation(&Operation108, { InputSlice { 1, 0, 8 }, InputSlice { 0, 0, 8 } }), BoundOperation(&Operation108, { InputSlice { 1, 8, 16 }, InputSlice { 0, 8, 16 } }), BoundOperation(&Operation108, { InputSlice { 1, 16, 24 }, InputSlice { 0, 16, 24 } }), BoundOperation(&Operation108, { InputSlice { 1, 24, 32 }, InputSlice { 0, 24, 32 } }), BoundOperation(&Operation108, { InputSlice { 1, 32, 40 }, InputSlice { 0, 32, 40 } }), BoundOperation(&Operation108, { InputSlice { 1, 40, 48 }, InputSlice { 0, 40, 48 } }), BoundOperation(&Operation108, { InputSlice { 1, 48, 56 }, InputSlice { 0, 48, 56 } }), BoundOperation(&Operation108, { InputSlice { 1, 56, 64 }, InputSlice { 0, 56, 64 } }) }, 1),
InstBinding("vabdl_s16", {  }, InstSignature { { 64, 64 }, { 128 }, false }, { BoundOperation(&Operation109, { InputSlice { 1, 0, 16 }, InputSlice { 0, 0, 16 } }), BoundOperation(&Operation109, { InputSlice { 1, 16, 32 }, InputSlice { 0, 16, 32 } }), BoundOperation(&Operation109, { InputSlice { 1, 32, 48 }, InputSlice { 0, 32, 48 } }), BoundOperation(&Operation109, { InputSlice { 1, 48, 64 }, InputSlice { 0, 48, 64 } }) }, 1),
InstBinding("vabdl_s32", {  }, InstSignature { { 64, 64 }, { 128 }, false }, { BoundOperation(&Operation110, { InputSlice { 1, 0, 32 }, InputSlice { 0, 0, 32 } }), BoundOperation(&Operation110, { InputSlice { 1, 32, 64 }, InputSlice { 0, 32, 64 } }) }, 1),
InstBinding("vabdl_u8", {  }, InstSignature { { 64, 64 }, { 128 }, false }, { BoundOperation(&Operation111, { InputSlice { 1, 0, 8 }, InputSlice { 0, 0, 8 } }), BoundOperation(&Operation111, { InputSlice { 1, 8, 16 }, InputSlice { 0, 8, 16 } }), BoundOperation(&Operation111, { InputSlice { 1, 16, 24 }, InputSlice { 0, 16, 24 } }), BoundOperation(&Operation111, { InputSlice { 1, 24, 32 }, InputSlice { 0, 24, 32 } }), BoundOperation(&Operation111, { InputSlice { 1, 32, 40 }, InputSlice { 0, 32, 40 } }), BoundOperation(&Operation111, { InputSlice { 1, 40, 48 }, InputSlice { 0, 40, 48 } }), BoundOperation(&Operation111, { InputSlice { 1, 48, 56 }, InputSlice { 0, 48, 56 } }), BoundOperation(&Operation111, { InputSlice { 1, 56, 64 }, InputSlice { 0, 56, 64 } }) }, 1),
InstBinding("vabdl_u16", {  }, InstSignature { { 64, 64 }, { 128 }, false }, { BoundOperation(&Operation112, { InputSlice { 1, 0, 16 }, InputSlice { 0, 0, 16 } }), BoundOperation(&Operation112, { InputSlice { 1, 16, 32 }, InputSlice { 0, 16, 32 } }), BoundOperation(&Operation112, { InputSlice { 1, 32, 48 }, InputSlice { 0, 32, 48 } }), BoundOperation(&Operation112, { InputSlice { 1, 48, 64 }, InputSlice { 0, 48, 64 } }) }, 1),
InstBinding("vabdl_u32", {  }, InstSignature { { 64, 64 }, { 128 }, false }, { BoundOperation(&Operation113, { InputSlice { 1, 0, 32 }, InputSlice { 0, 0, 32 } }), BoundOperation(&Operation113, { InputSlice { 1, 32, 64 }, InputSlice { 0, 32, 64 } }) }, 1),
InstBinding("vaba_s8", {  }, InstSignature { { 64, 64, 64 }, { 64 }, false }, { BoundOperation(&Operation114, { InputSlice { 2, 0, 8 }, InputSlice { 1, 0, 8 }, InputSlice { 0, 0, 8 } }), BoundOperation(&Operation114, { InputSlice { 2, 8, 16 }, InputSlice { 1, 8, 16 }, InputSlice { 0, 8, 16 } }), BoundOperation(&Operation114, { InputSlice { 2, 16, 24 }, InputSlice { 1, 16, 24 }, InputSlice { 0, 16, 24 } }), BoundOperation(&Operation114, { InputSlice { 2, 24, 32 }, InputSlice { 1, 24, 32 }, InputSlice { 0, 24, 32 } }), BoundOperation(&Operation114, { InputSlice { 2, 32, 40 }, InputSlice { 1, 32, 40 }, InputSlice { 0, 32, 40 } }), BoundOperation(&Operation114, { InputSlice { 2, 40, 48 }, InputSlice { 1, 40, 48 }, InputSlice { 0, 40, 48 } }), BoundOperation(&Operation114, { InputSlice { 2, 48, 56 }, InputSlice { 1, 48, 56 }, InputSlice { 0, 48, 56 } }), BoundOperation(&Operation114, { InputSlice { 2, 56, 64 }, InputSlice { 1, 56, 64 }, InputSlice { 0, 56, 64 } }) }, 1),
InstBinding("vaba_s16", {  }, InstSignature { { 64, 64, 64 }, { 64 }, false }, { BoundOperation(&Operation115, { InputSlice { 2, 0, 16 }, InputSlice { 1, 0, 16 }, InputSlice { 0, 0, 16 } }), BoundOperation(&Operation115, { InputSlice { 2, 16, 32 }, InputSlice { 1, 16, 32 }, InputSlice { 0, 16, 32 } }), BoundOperation(&Operation115, { InputSlice { 2, 32, 48 }, InputSlice { 1, 32, 48 }, InputSlice { 0, 32, 48 } }), BoundOperation(&Operation115, { InputSlice { 2, 48, 64 }, InputSlice { 1, 48, 64 }, InputSlice { 0, 48, 64 } }) }, 1),
InstBinding("vaba_s32", {  }, InstSignature { { 64, 64, 64 }, { 64 }, false }, { BoundOperation(&Operation116, { InputSlice { 2, 0, 32 }, InputSlice { 1, 0, 32 }, InputSlice { 0, 0, 32 } }), BoundOperation(&Operation116, { InputSlice { 2, 32, 64 }, InputSlice { 1, 32, 64 }, InputSlice { 0, 32, 64 } }) }, 1),
InstBinding("vaba_u8", {  }, InstSignature { { 64, 64, 64 }, { 64 }, false }, { BoundOperation(&Operation117, { InputSlice { 2, 0, 8 }, InputSlice { 1, 0, 8 }, InputSlice { 0, 0, 8 } }), BoundOperation(&Operation117, { InputSlice { 2, 8, 16 }, InputSlice { 1, 8, 16 }, InputSlice { 0, 8, 16 } }), BoundOperation(&Operation117, { InputSlice { 2, 16, 24 }, InputSlice { 1, 16, 24 }, InputSlice { 0, 16, 24 } }), BoundOperation(&Operation117, { InputSlice { 2, 24, 32 }, InputSlice { 1, 24, 32 }, InputSlice { 0, 24, 32 } }), BoundOperation(&Operation117, { InputSlice { 2, 32, 40 }, InputSlice { 1, 32, 40 }, InputSlice { 0, 32, 40 } }), BoundOperation(&Operation117, { InputSlice { 2, 40, 48 }, InputSlice { 1, 40, 48 }, InputSlice { 0, 40, 48 } }), BoundOperation(&Operation117, { InputSlice { 2, 48, 56 }, InputSlice { 1, 48, 56 }, InputSlice { 0, 48, 56 } }), BoundOperation(&Operation117, { InputSlice { 2, 56, 64 }, InputSlice { 1, 56, 64 }, InputSlice { 0, 56, 64 } }) }, 1),
InstBinding("vaba_u16", {  }, InstSignature { { 64, 64, 64 }, { 64 }, false }, { BoundOperation(&Operation118, { InputSlice { 2, 0, 16 }, InputSlice { 1, 0, 16 }, InputSlice { 0, 0, 16 } }), BoundOperation(&Operation118, { InputSlice { 2, 16, 32 }, InputSlice { 1, 16, 32 }, InputSlice { 0, 16, 32 } }), BoundOperation(&Operation118, { InputSlice { 2, 32, 48 }, InputSlice { 1, 32, 48 }, InputSlice { 0, 32, 48 } }), BoundOperation(&Operation118, { InputSlice { 2, 48, 64 }, InputSlice { 1, 48, 64 }, InputSlice { 0, 48, 64 } }) }, 1),
InstBinding("vaba_u32", {  }, InstSignature { { 64, 64, 64 }, { 64 }, false }, { BoundOperation(&Operation119, { InputSlice { 2, 0, 32 }, InputSlice { 1, 0, 32 }, InputSlice { 0, 0, 32 } }), BoundOperation(&Operation119, { InputSlice { 2, 32, 64 }, InputSlice { 1, 32, 64 }, InputSlice { 0, 32, 64 } }) }, 1),
InstBinding("vabaq_s8", {  }, InstSignature { { 128, 128, 128 }, { 128 }, false }, { BoundOperation(&Operation114, { InputSlice { 2, 0, 8 }, InputSlice { 1, 0, 8 }, InputSlice { 0, 0, 8 } }), BoundOperation(&Operation114, { InputSlice { 2, 8, 16 }, InputSlice { 1, 8, 16 }, InputSlice { 0, 8, 16 } }), BoundOperation(&Operation114, { InputSlice { 2, 16, 24 }, InputSlice { 1, 16, 24 }, InputSlice { 0, 16, 24 } }), BoundOperation(&Operation114, { InputSlice { 2, 24, 32 }, InputSlice { 1, 24, 32 }, InputSlice { 0, 24, 32 } }), BoundOperation(&Operation114, { InputSlice { 2, 32, 40 }, InputSlice { 1, 32, 40 }, InputSlice { 0, 32, 40 } }), BoundOperation(&Operation114, { InputSlice { 2, 40, 48 }, InputSlice { 1, 40, 48 }, InputSlice { 0, 40, 48 } }), BoundOperation(&Operation114, { InputSlice { 2, 48, 56 }, InputSlice { 1, 48, 56 }, InputSlice { 0, 48, 56 } }), BoundOperation(&Operation114, { InputSlice { 2, 56, 64 }, InputSlice { 1, 56, 64 }, InputSlice { 0, 56, 64 } }), BoundOperation(&Operation114, { InputSlice { 2, 64, 72 }, InputSlice { 1, 64, 72 }, InputSlice { 0, 64, 72 } }), BoundOperation(&Operation114, { InputSlice { 2, 72, 80 }, InputSlice { 1, 72, 80 }, InputSlice { 0, 72, 80 } }), BoundOperation(&Operation114, { InputSlice { 2, 80, 88 }, InputSlice { 1, 80, 88 }, InputSlice { 0, 80, 88 } }), BoundOperation(&Operation114, { InputSlice { 2, 88, 96 }, InputSlice { 1, 88, 96 }, InputSlice { 0, 88, 96 } }), BoundOperation(&Operation114, { InputSlice { 2, 96, 104 }, InputSlice { 1, 96, 104 }, InputSlice { 0, 96, 104 } }), BoundOperation(&Operation114, { InputSlice { 2, 104, 112 }, InputSlice { 1, 104, 112 }, InputSlice { 0, 104, 112 } }), BoundOperation(&Operation114, { InputSlice { 2, 112, 120 }, InputSlice { 1, 112, 120 }, InputSlice { 0, 112, 120 } }), BoundOperation(&Operation114, { InputSlice { 2, 120, 128 }, InputSlice { 1, 120, 128 }, InputSlice { 0, 120, 128 } }) }, 1),
InstBinding("vabaq_s16", {  }, InstSignature { { 128, 128, 128 }, { 128 }, false }, { BoundOperation(&Operation115, { InputSlice { 2, 0, 16 }, InputSlice { 1, 0, 16 }, InputSlice { 0, 0, 16 } }), BoundOperation(&Operation115, { InputSlice { 2, 16, 32 }, InputSlice { 1, 16, 32 }, InputSlice { 0, 16, 32 } }), BoundOperation(&Operation115, { InputSlice { 2, 32, 48 }, InputSlice { 1, 32, 48 }, InputSlice { 0, 32, 48 } }), BoundOperation(&Operation115, { InputSlice { 2, 48, 64 }, InputSlice { 1, 48, 64 }, InputSlice { 0, 48, 64 } }), BoundOperation(&Operation115, { InputSlice { 2, 64, 80 }, InputSlice { 1, 64, 80 }, InputSlice { 0, 64, 80 } }), BoundOperation(&Operation115, { InputSlice { 2, 80, 96 }, InputSlice { 1, 80, 96 }, InputSlice { 0, 80, 96 } }), BoundOperation(&Operation115, { InputSlice { 2, 96, 112 }, InputSlice { 1, 96, 112 }, InputSlice { 0, 96, 112 } }), BoundOperation(&Operation115, { InputSlice { 2, 112, 128 }, InputSlice { 1, 112, 128 }, InputSlice { 0, 112, 128 } }) }, 1),
InstBinding("vabaq_s32", {  }, InstSignature { { 128, 128, 128 }, { 128 }, false }, { BoundOperation(&Operation116, { InputSlice { 2, 0, 32 }, InputSlice { 1, 0, 32 }, InputSlice { 0, 0, 32 } }), BoundOperation(&Operation116, { InputSlice { 2, 32, 64 }, InputSlice { 1, 32, 64 }, InputSlice { 0, 32, 64 } }), BoundOperation(&Operation116, { InputSlice { 2, 64, 96 }, InputSlice { 1, 64, 96 }, InputSlice { 0, 64, 96 } }), BoundOperation(&Operation116, { InputSlice { 2, 96, 128 }, InputSlice { 1, 96, 128 }, InputSlice { 0, 96, 128 } }) }, 1),
InstBinding("vabaq_u8", {  }, InstSignature { { 128, 128, 128 }, { 128 }, false }, { BoundOperation(&Operation117, { InputSlice { 2, 0, 8 }, InputSlice { 1, 0, 8 }, InputSlice { 0, 0, 8 } }), BoundOperation(&Operation117, { InputSlice { 2, 8, 16 }, InputSlice { 1, 8, 16 }, InputSlice { 0, 8, 16 } }), BoundOperation(&Operation117, { InputSlice { 2, 16, 24 }, InputSlice { 1, 16, 24 }, InputSlice { 0, 16, 24 } }), BoundOperation(&Operation117, { InputSlice { 2, 24, 32 }, InputSlice { 1, 24, 32 }, InputSlice { 0, 24, 32 } }), BoundOperation(&Operation117, { InputSlice { 2, 32, 40 }, InputSlice { 1, 32, 40 }, InputSlice { 0, 32, 40 } }), BoundOperation(&Operation117, { InputSlice { 2, 40, 48 }, InputSlice { 1, 40, 48 }, InputSlice { 0, 40, 48 } }), BoundOperation(&Operation117, { InputSlice { 2, 48, 56 }, InputSlice { 1, 48, 56 }, InputSlice { 0, 48, 56 } }), BoundOperation(&Operation117, { InputSlice { 2, 56, 64 }, InputSlice { 1, 56, 64 }, InputSlice { 0, 56, 64 } }), BoundOperation(&Operation117, { InputSlice { 2, 64, 72 }, InputSlice { 1, 64, 72 }, InputSlice { 0, 64, 72 } }), BoundOperation(&Operation117, { InputSlice { 2, 72, 80 }, InputSlice { 1, 72, 80 }, InputSlice { 0, 72, 80 } }), BoundOperation(&Operation117, { InputSlice { 2, 80, 88 }, InputSlice { 1, 80, 88 }, InputSlice { 0, 80, 88 } }), BoundOperation(&Operation117, { InputSlice { 2, 88, 96 }, InputSlice { 1, 88, 96 }, InputSlice { 0, 88, 96 } }), BoundOperation(&Operation117, { InputSlice { 2, 96, 104 }, InputSlice { 1, 96, 104 }, InputSlice { 0, 96, 104 } }), BoundOperation(&Operation117, { InputSlice { 2, 104, 112 }, InputSlice { 1, 104, 112 }, InputSlice { 0, 104, 112 } }), BoundOperation(&Operation117, { InputSlice { 2, 112, 120 }, InputSlice { 1, 112, 120 }, InputSlice { 0, 112, 120 } }), BoundOperation(&Operation117, { InputSlice { 2, 120, 128 }, InputSlice { 1, 120, 128 }, InputSlice { 0, 120, 128 } }) }, 1),
InstBinding("vabaq_u16", {  }, InstSignature { { 128, 128, 128 }, { 128 }, false }, { BoundOperation(&Operation118, { InputSlice { 2, 0, 16 }, InputSlice { 1, 0, 16 }, InputSlice { 0, 0, 16 } }), BoundOperation(&Operation118, { InputSlice { 2, 16, 32 }, InputSlice { 1, 16, 32 }, InputSlice { 0, 16, 32 } }), BoundOperation(&Operation118, { InputSlice { 2, 32, 48 }, InputSlice { 1, 32, 48 }, InputSlice { 0, 32, 48 } }), BoundOperation(&Operation118, { InputSlice { 2, 48, 64 }, InputSlice { 1, 48, 64 }, InputSlice { 0, 48, 64 } }), BoundOperation(&Operation118, { InputSlice { 2, 64, 80 }, InputSlice { 1, 64, 80 }, InputSlice { 0, 64, 80 } }), BoundOperation(&Operation118, { InputSlice { 2, 80, 96 }, InputSlice { 1, 80, 96 }, InputSlice { 0, 80, 96 } }), BoundOperation(&Operation118, { InputSlice { 2, 96, 112 }, InputSlice { 1, 96, 112 }, InputSlice { 0, 96, 112 } }), BoundOperation(&Operation118, { InputSlice { 2, 112, 128 }, InputSlice { 1, 112, 128 }, InputSlice { 0, 112, 128 } }) }, 1),
InstBinding("vabaq_u32", {  }, InstSignature { { 128, 128, 128 }, { 128 }, false }, { BoundOperation(&Operation119, { InputSlice { 2, 0, 32 }, InputSlice { 1, 0, 32 }, InputSlice { 0, 0, 32 } }), BoundOperation(&Operation119, { InputSlice { 2, 32, 64 }, InputSlice { 1, 32, 64 }, InputSlice { 0, 32, 64 } }), BoundOperation(&Operation119, { InputSlice { 2, 64, 96 }, InputSlice { 1, 64, 96 }, InputSlice { 0, 64, 96 } }), BoundOperation(&Operation119, { InputSlice { 2, 96, 128 }, InputSlice { 1, 96, 128 }, InputSlice { 0, 96, 128 } }) }, 1),
InstBinding("vabal_s8", {  }, InstSignature { { 128, 64, 64 }, { 128 }, false }, { BoundOperation(&Operation120, { InputSlice { 2, 0, 8 }, InputSlice { 1, 0, 8 }, InputSlice { 0, 0, 16 } }), BoundOperation(&Operation120, { InputSlice { 2, 8, 16 }, InputSlice { 1, 8, 16 }, InputSlice { 0, 16, 32 } }), BoundOperation(&Operation120, { InputSlice { 2, 16, 24 }, InputSlice { 1, 16, 24 }, InputSlice { 0, 32, 48 } }), BoundOperation(&Operation120, { InputSlice { 2, 24, 32 }, InputSlice { 1, 24, 32 }, InputSlice { 0, 48, 64 } }), BoundOperation(&Operation120, { InputSlice { 2, 32, 40 }, InputSlice { 1, 32, 40 }, InputSlice { 0, 64, 80 } }), BoundOperation(&Operation120, { InputSlice { 2, 40, 48 }, InputSlice { 1, 40, 48 }, InputSlice { 0, 80, 96 } }), BoundOperation(&Operation120, { InputSlice { 2, 48, 56 }, InputSlice { 1, 48, 56 }, InputSlice { 0, 96, 112 } }), BoundOperation(&Operation120, { InputSlice { 2, 56, 64 }, InputSlice { 1, 56, 64 }, InputSlice { 0, 112, 128 } }) }, 1),
InstBinding("vabal_s16", {  }, InstSignature { { 128, 64, 64 }, { 128 }, false }, { BoundOperation(&Operation121, { InputSlice { 2, 0, 16 }, InputSlice { 1, 0, 16 }, InputSlice { 0, 0, 32 } }), BoundOperation(&Operation121, { InputSlice { 2, 16, 32 }, InputSlice { 1, 16, 32 }, InputSlice { 0, 32, 64 } }), BoundOperation(&Operation121, { InputSlice { 2, 32, 48 }, InputSlice { 1, 32, 48 }, InputSlice { 0, 64, 96 } }), BoundOperation(&Operation121, { InputSlice { 2, 48, 64 }, InputSlice { 1, 48, 64 }, InputSlice { 0, 96, 128 } }) }, 1),
InstBinding("vabal_s32", {  }, InstSignature { { 128, 64, 64 }, { 128 }, false }, { BoundOperation(&Operation122, { InputSlice { 2, 0, 32 }, InputSlice { 1, 0, 32 }, InputSlice { 0, 0, 64 } }), BoundOperation(&Operation122, { InputSlice { 2, 32, 64 }, InputSlice { 1, 32, 64 }, InputSlice { 0, 64, 128 } }) }, 1),
InstBinding("vabal_u8", {  }, InstSignature { { 128, 64, 64 }, { 128 }, false }, { BoundOperation(&Operation123, { InputSlice { 2, 0, 8 }, InputSlice { 1, 0, 8 }, InputSlice { 0, 0, 16 } }), BoundOperation(&Operation123, { InputSlice { 2, 8, 16 }, InputSlice { 1, 8, 16 }, InputSlice { 0, 16, 32 } }), BoundOperation(&Operation123, { InputSlice { 2, 16, 24 }, InputSlice { 1, 16, 24 }, InputSlice { 0, 32, 48 } }), BoundOperation(&Operation123, { InputSlice { 2, 24, 32 }, InputSlice { 1, 24, 32 }, InputSlice { 0, 48, 64 } }), BoundOperation(&Operation123, { InputSlice { 2, 32, 40 }, InputSlice { 1, 32, 40 }, InputSlice { 0, 64, 80 } }), BoundOperation(&Operation123, { InputSlice { 2, 40, 48 }, InputSlice { 1, 40, 48 }, InputSlice { 0, 80, 96 } }), BoundOperation(&Operation123, { InputSlice { 2, 48, 56 }, InputSlice { 1, 48, 56 }, InputSlice { 0, 96, 112 } }), BoundOperation(&Operation123, { InputSlice { 2, 56, 64 }, InputSlice { 1, 56, 64 }, InputSlice { 0, 112, 128 } }) }, 1),
InstBinding("vabal_u16", {  }, InstSignature { { 128, 64, 64 }, { 128 }, false }, { BoundOperation(&Operation124, { InputSlice { 2, 0, 16 }, InputSlice { 1, 0, 16 }, InputSlice { 0, 0, 32 } }), BoundOperation(&Operation124, { InputSlice { 2, 16, 32 }, InputSlice { 1, 16, 32 }, InputSlice { 0, 32, 64 } }), BoundOperation(&Operation124, { InputSlice { 2, 32, 48 }, InputSlice { 1, 32, 48 }, InputSlice { 0, 64, 96 } }), BoundOperation(&Operation124, { InputSlice { 2, 48, 64 }, InputSlice { 1, 48, 64 }, InputSlice { 0, 96, 128 } }) }, 1),
InstBinding("vabal_u32", {  }, InstSignature { { 128, 64, 64 }, { 128 }, false }, { BoundOperation(&Operation125, { InputSlice { 2, 0, 32 }, InputSlice { 1, 0, 32 }, InputSlice { 0, 0, 64 } }), BoundOperation(&Operation125, { InputSlice { 2, 32, 64 }, InputSlice { 1, 32, 64 }, InputSlice { 0, 64, 128 } }) }, 1),
InstBinding("vmax_s8", {  }, InstSignature { { 64, 64 }, { 64 }, false }, { BoundOperation(&Operation126, { InputSlice { 1, 0, 8 }, InputSlice { 0, 0, 8 } }), BoundOperation(&Operation126, { InputSlice { 1, 8, 16 }, InputSlice { 0, 8, 16 } }), BoundOperation(&Operation126, { InputSlice { 1, 16, 24 }, InputSlice { 0, 16, 24 } }), BoundOperation(&Operation126, { InputSlice { 1, 24, 32 }, InputSlice { 0, 24, 32 } }), BoundOperation(&Operation126, { InputSlice { 1, 32, 40 }, InputSlice { 0, 32, 40 } }), BoundOperation(&Operation126, { InputSlice { 1, 40, 48 }, InputSlice { 0, 40, 48 } }), BoundOperation(&Operation126, { InputSlice { 1, 48, 56 }, InputSlice { 0, 48, 56 } }), BoundOperation(&Operation126, { InputSlice { 1, 56, 64 }, InputSlice { 0, 56, 64 } }) }, 1),
InstBinding("vmax_s16", {  }, InstSignature { { 64, 64 }, { 64 }, false }, { BoundOperation(&Operation127, { InputSlice { 1, 0, 16 }, InputSlice { 0, 0, 16 } }), BoundOperation(&Operation127, { InputSlice { 1, 16, 32 }, InputSlice { 0, 16, 32 } }), BoundOperation(&Operation127, { InputSlice { 1, 32, 48 }, InputSlice { 0, 32, 48 } }), BoundOperation(&Operation127, { InputSlice { 1, 48, 64 }, InputSlice { 0, 48, 64 } }) }, 1),
InstBinding("vmax_s32", {  }, InstSignature { { 64, 64 }, { 64 }, false }, { BoundOperation(&Operation128, { InputSlice { 1, 0, 32 }, InputSlice { 0, 0, 32 } }), BoundOperation(&Operation128, { InputSlice { 1, 32, 64 }, InputSlice { 0, 32, 64 } }) }, 1),
InstBinding("vmax_u8", {  }, InstSignature { { 64, 64 }, { 64 }, false }, { BoundOperation(&Operation129, { InputSlice { 1, 0, 8 }, InputSlice { 0, 0, 8 } }), BoundOperation(&Operation129, { InputSlice { 1, 8, 16 }, InputSlice { 0, 8, 16 } }), BoundOperation(&Operation129, { InputSlice { 1, 16, 24 }, InputSlice { 0, 16, 24 } }), BoundOperation(&Operation129, { InputSlice { 1, 24, 32 }, InputSlice { 0, 24, 32 } }), BoundOperation(&Operation129, { InputSlice { 1, 32, 40 }, InputSlice { 0, 32, 40 } }), BoundOperation(&Operation129, { InputSlice { 1, 40, 48 }, InputSlice { 0, 40, 48 } }), BoundOperation(&Operation129, { InputSlice { 1, 48, 56 }, InputSlice { 0, 48, 56 } }), BoundOperation(&Operation129, { InputSlice { 1, 56, 64 }, InputSlice { 0, 56, 64 } }) }, 1),
InstBinding("vmax_u16", {  }, InstSignature { { 64, 64 }, { 64 }, false }, { BoundOperation(&Operation130, { InputSlice { 1, 0, 16 }, InputSlice { 0, 0, 16 } }), BoundOperation(&Operation130, { InputSlice { 1, 16, 32 }, InputSlice { 0, 16, 32 } }), BoundOperation(&Operation130, { InputSlice { 1, 32, 48 }, InputSlice { 0, 32, 48 } }), BoundOperation(&Operation130, { InputSlice { 1, 48, 64 }, InputSlice { 0, 48, 64 } }) }, 1),
InstBinding("vmax_u32", {  }, InstSignature { { 64, 64 }, { 64 }, false }, { BoundOperation(&Operation131, { InputSlice { 1, 0, 32 }, InputSlice { 0, 0, 32 } }), BoundOperation(&Operation131, { InputSlice { 1, 32, 64 }, InputSlice { 0, 32, 64 } }) }, 1),
InstBinding("vmax_f32", {  }, InstSignature { { 64, 64 }, { 64 }, false }, { BoundOperation(&Operation132, { InputSlice { 0, 0, 32 }, InputSlice { 1, 0, 32 } }), BoundOperation(&Operation132, { InputSlice { 0, 32, 64 }, InputSlice { 1, 32, 64 } }) }, 1),
InstBinding("vmaxq_s8", {  }, InstSignature { { 128, 128 }, { 128 }, false }, { BoundOperation(&Operation126, { InputSlice { 1, 0, 8 }, InputSlice { 0, 0, 8 } }), BoundOperation(&Operation126, { InputSlice { 1, 8, 16 }, InputSlice { 0, 8, 16 } }), BoundOperation(&Operation126, { InputSlice { 1, 16, 24 }, InputSlice { 0, 16, 24 } }), BoundOperation(&Operation126, { InputSlice { 1, 24, 32 }, InputSlice { 0, 24, 32 } }), BoundOperation(&Operation126, { InputSlice { 1, 32, 40 }, InputSlice { 0, 32, 40 } }), BoundOperation(&Operation126, { InputSlice { 1, 40, 48 }, InputSlice { 0, 40, 48 } }), BoundOperation(&Operation126, { InputSlice { 1, 48, 56 }, InputSlice { 0, 48, 56 } }), BoundOperation(&Operation126, { InputSlice { 1, 56, 64 }, InputSlice { 0, 56, 64 } }), BoundOperation(&Operation126, { InputSlice { 1, 64, 72 }, InputSlice { 0, 64, 72 } }), BoundOperation(&Operation126, { InputSlice { 1, 72, 80 }, InputSlice { 0, 72, 80 } }), BoundOperation(&Operation126, { InputSlice { 1, 80, 88 }, InputSlice { 0, 80, 88 } }), BoundOperation(&Operation126, { InputSlice { 1, 88, 96 }, InputSlice { 0, 88, 96 } }), BoundOperation(&Operation126, { InputSlice { 1, 96, 104 }, InputSlice { 0, 96, 104 } }), BoundOperation(&Operation126, { InputSlice { 1, 104, 112 }, InputSlice { 0, 104, 112 } }), BoundOperation(&Operation126, { InputSlice { 1, 112, 120 }, InputSlice { 0, 112, 120 } }), BoundOperation(&Operation126, { InputSlice { 1, 120, 128 }, InputSlice { 0, 120, 128 } }) }, 1),
InstBinding("vmaxq_s16", {  }, InstSignature { { 128, 128 }, { 128 }, false }, { BoundOperation(&Operation127, { InputSlice { 1, 0, 16 }, InputSlice { 0, 0, 16 } }), BoundOperation(&Operation127, { InputSlice { 1, 16, 32 }, InputSlice { 0, 16, 32 } }), BoundOperation(&Operation127, { InputSlice { 1, 32, 48 }, InputSlice { 0, 32, 48 } }), BoundOperation(&Operation127, { InputSlice { 1, 48, 64 }, InputSlice { 0, 48, 64 } }), BoundOperation(&Operation127, { InputSlice { 1, 64, 80 }, InputSlice { 0, 64, 80 } }), BoundOperation(&Operation127, { InputSlice { 1, 80, 96 }, InputSlice { 0, 80, 96 } }), BoundOperation(&Operation127, { InputSlice { 1, 96, 112 }, InputSlice { 0, 96, 112 } }), BoundOperation(&Operation127, { InputSlice { 1, 112, 128 }, InputSlice { 0, 112, 128 } }) }, 1),
InstBinding("vmaxq_s32", {  }, InstSignature { { 128, 128 }, { 128 }, false }, { BoundOperation(&Operation128, { InputSlice { 1, 0, 32 }, InputSlice { 0, 0, 32 } }), BoundOperation(&Operation128, { InputSlice { 1, 32, 64 }, InputSlice { 0, 32, 64 } }), BoundOperation(&Operation128, { InputSlice { 1, 64, 96 }, InputSlice { 0, 64, 96 } }), BoundOperation(&Operation128, { InputSlice { 1, 96, 128 }, InputSlice { 0, 96, 128 } }) }, 1),
InstBinding("vmaxq_u8", {  }, InstSignature { { 128, 128 }, { 128 }, false }, { BoundOperation(&Operation129, { InputSlice { 1, 0, 8 }, InputSlice { 0, 0, 8 } }), BoundOperation(&Operation129, { InputSlice { 1, 8, 16 }, InputSlice { 0, 8, 16 } }), BoundOperation(&Operation129, { InputSlice { 1, 16, 24 }, InputSlice { 0, 16, 24 } }), BoundOperation(&Operation129, { InputSlice { 1, 24, 32 }, InputSlice { 0, 24, 32 } }), BoundOperation(&Operation129, { InputSlice { 1, 32, 40 }, InputSlice { 0, 32, 40 } }), BoundOperation(&Operation129, { InputSlice { 1, 40, 48 }, InputSlice { 0, 40, 48 } }), BoundOperation(&Operation129, { InputSlice { 1, 48, 56 }, InputSlice { 0, 48, 56 } }), BoundOperation(&Operation129, { InputSlice { 1, 56, 64 }, InputSlice { 0, 56, 64 } }), BoundOperation(&Operation129, { InputSlice { 1, 64, 72 }, InputSlice { 0, 64, 72 } }), BoundOperation(&Operation129, { InputSlice { 1, 72, 80 }, InputSlice { 0, 72, 80 } }), BoundOperation(&Operation129, { InputSlice { 1, 80, 88 }, InputSlice { 0, 80, 88 } }), BoundOperation(&Operation129, { InputSlice { 1, 88, 96 }, InputSlice { 0, 88, 96 } }), BoundOperation(&Operation129, { InputSlice { 1, 96, 104 }, InputSlice { 0, 96, 104 } }), BoundOperation(&Operation129, { InputSlice { 1, 104, 112 }, InputSlice { 0, 104, 112 } }), BoundOperation(&Operation129, { InputSlice { 1, 112, 120 }, InputSlice { 0, 112, 120 } }), BoundOperation(&Operation129, { InputSlice { 1, 120, 128 }, InputSlice { 0, 120, 128 } }) }, 1),
InstBinding("vmaxq_u16", {  }, InstSignature { { 128, 128 }, { 128 }, false }, { BoundOperation(&Operation130, { InputSlice { 1, 0, 16 }, InputSlice { 0, 0, 16 } }), BoundOperation(&Operation130, { InputSlice { 1, 16, 32 }, InputSlice { 0, 16, 32 } }), BoundOperation(&Operation130, { InputSlice { 1, 32, 48 }, InputSlice { 0, 32, 48 } }), BoundOperation(&Operation130, { InputSlice { 1, 48, 64 }, InputSlice { 0, 48, 64 } }), BoundOperation(&Operation130, { InputSlice { 1, 64, 80 }, InputSlice { 0, 64, 80 } }), BoundOperation(&Operation130, { InputSlice { 1, 80, 96 }, InputSlice { 0, 80, 96 } }), BoundOperation(&Operation130, { InputSlice { 1, 96, 112 }, InputSlice { 0, 96, 112 } }), BoundOperation(&Operation130, { InputSlice { 1, 112, 128 }, InputSlice { 0, 112, 128 } }) }, 1),
InstBinding("vmaxq_u32", {  }, InstSignature { { 128, 128 }, { 128 }, false }, { BoundOperation(&Operation131, { InputSlice { 1, 0, 32 }, InputSlice { 0, 0, 32 } }), BoundOperation(&Operation131, { InputSlice { 1, 32, 64 }, InputSlice { 0, 32, 64 } }), BoundOperation(&Operation131, { InputSlice { 1, 64, 96 }, InputSlice { 0, 64, 96 } }), BoundOperation(&Operation131, { InputSlice { 1, 96, 128 }, InputSlice { 0, 96, 128 } }) }, 1),
InstBinding("vmaxq_f32", {  }, InstSignature { { 128, 128 }, { 128 }, false }, { BoundOperation(&Operation132, { InputSlice { 0, 0, 32 }, InputSlice { 1, 0, 32 } }), BoundOperation(&Operation132, { InputSlice { 0, 32, 64 }, InputSlice { 1, 32, 64 } }), BoundOperation(&Operation132, { InputSlice { 0, 64, 96 }, InputSlice { 1, 64, 96 } }), BoundOperation(&Operation132, { InputSlice { 0, 96, 128 }, InputSlice { 1, 96, 128 } }) }, 1),
InstBinding("vmin_s8", {  }, InstSignature { { 64, 64 }, { 64 }, false }, { BoundOperation(&Operation133, { InputSlice { 1, 0, 8 }, InputSlice { 0, 0, 8 } }), BoundOperation(&Operation133, { InputSlice { 1, 8, 16 }, InputSlice { 0, 8, 16 } }), BoundOperation(&Operation133, { InputSlice { 1, 16, 24 }, InputSlice { 0, 16, 24 } }), BoundOperation(&Operation133, { InputSlice { 1, 24, 32 }, InputSlice { 0, 24, 32 } }), BoundOperation(&Operation133, { InputSlice { 1, 32, 40 }, InputSlice { 0, 32, 40 } }), BoundOperation(&Operation133, { InputSlice { 1, 40, 48 }, InputSlice { 0, 40, 48 } }), BoundOperation(&Operation133, { InputSlice { 1, 48, 56 }, InputSlice { 0, 48, 56 } }), BoundOperation(&Operation133, { InputSlice { 1, 56, 64 }, InputSlice { 0, 56, 64 } }) }, 1),
InstBinding("vmin_s16", {  }, InstSignature { { 64, 64 }, { 64 }, false }, { BoundOperation(&Operation134, { InputSlice { 1, 0, 16 }, InputSlice { 0, 0, 16 } }), BoundOperation(&Operation134, { InputSlice { 1, 16, 32 }, InputSlice { 0, 16, 32 } }), BoundOperation(&Operation134, { InputSlice { 1, 32, 48 }, InputSlice { 0, 32, 48 } }), BoundOperation(&Operation134, { InputSlice { 1, 48, 64 }, InputSlice { 0, 48, 64 } }) }, 1),
InstBinding("vmin_s32", {  }, InstSignature { { 64, 64 }, { 64 }, false }, { BoundOperation(&Operation135, { InputSlice { 1, 0, 32 }, InputSlice { 0, 0, 32 } }), BoundOperation(&Operation135, { InputSlice { 1, 32, 64 }, InputSlice { 0, 32, 64 } }) }, 1),
InstBinding("vmin_u8", {  }, InstSignature { { 64, 64 }, { 64 }, false }, { BoundOperation(&Operation136, { InputSlice { 1, 0, 8 }, InputSlice { 0, 0, 8 } }), BoundOperation(&Operation136, { InputSlice { 1, 8, 16 }, InputSlice { 0, 8, 16 } }), BoundOperation(&Operation136, { InputSlice { 1, 16, 24 }, InputSlice { 0, 16, 24 } }), BoundOperation(&Operation136, { InputSlice { 1, 24, 32 }, InputSlice { 0, 24, 32 } }), BoundOperation(&Operation136, { InputSlice { 1, 32, 40 }, InputSlice { 0, 32, 40 } }), BoundOperation(&Operation136, { InputSlice { 1, 40, 48 }, InputSlice { 0, 40, 48 } }), BoundOperation(&Operation136, { InputSlice { 1, 48, 56 }, InputSlice { 0, 48, 56 } }), BoundOperation(&Operation136, { InputSlice { 1, 56, 64 }, InputSlice { 0, 56, 64 } }) }, 1),
InstBinding("vmin_u16", {  }, InstSignature { { 64, 64 }, { 64 }, false }, { BoundOperation(&Operation137, { InputSlice { 1, 0, 16 }, InputSlice { 0, 0, 16 } }), BoundOperation(&Operation137, { InputSlice { 1, 16, 32 }, InputSlice { 0, 16, 32 } }), BoundOperation(&Operation137, { InputSlice { 1, 32, 48 }, InputSlice { 0, 32, 48 } }), BoundOperation(&Operation137, { InputSlice { 1, 48, 64 }, InputSlice { 0, 48, 64 } }) }, 1),
InstBinding("vmin_u32", {  }, InstSignature { { 64, 64 }, { 64 }, false }, { BoundOperation(&Operation138, { InputSlice { 1, 0, 32 }, InputSlice { 0, 0, 32 } }), BoundOperation(&Operation138, { InputSlice { 1, 32, 64 }, InputSlice { 0, 32, 64 } }) }, 1),
InstBinding("vmin_f32", {  }, InstSignature { { 64, 64 }, { 64 }, false }, { BoundOperation(&Operation139, { InputSlice { 0, 0, 32 }, InputSlice { 1, 0, 32 } }), BoundOperation(&Operation139, { InputSlice { 0, 32, 64 }, InputSlice { 1, 32, 64 } }) }, 1),
InstBinding("vminq_s8", {  }, InstSignature { { 128, 128 }, { 128 }, false }, { BoundOperation(&Operation133, { InputSlice { 1, 0, 8 }, InputSlice { 0, 0, 8 } }), BoundOperation(&Operation133, { InputSlice { 1, 8, 16 }, InputSlice { 0, 8, 16 } }), BoundOperation(&Operation133, { InputSlice { 1, 16, 24 }, InputSlice { 0, 16, 24 } }), BoundOperation(&Operation133, { InputSlice { 1, 24, 32 }, InputSlice { 0, 24, 32 } }), BoundOperation(&Operation133, { InputSlice { 1, 32, 40 }, InputSlice { 0, 32, 40 } }), BoundOperation(&Operation133, { InputSlice { 1, 40, 48 }, InputSlice { 0, 40, 48 } }), BoundOperation(&Operation133, { InputSlice { 1, 48, 56 }, InputSlice { 0, 48, 56 } }), BoundOperation(&Operation133, { InputSlice { 1, 56, 64 }, InputSlice { 0, 56, 64 } }), BoundOperation(&Operation133, { InputSlice { 1, 64, 72 }, InputSlice { 0, 64, 72 } }), BoundOperation(&Operation133, { InputSlice { 1, 72, 80 }, InputSlice { 0, 72, 80 } }), BoundOperation(&Operation133, { InputSlice { 1, 80, 88 }, InputSlice { 0, 80, 88 } }), BoundOperation(&Operation133, { InputSlice { 1, 88, 96 }, InputSlice { 0, 88, 96 } }), BoundOperation(&Operation133, { InputSlice { 1, 96, 104 }, InputSlice { 0, 96, 104 } }), BoundOperation(&Operation133, { InputSlice { 1, 104, 112 }, InputSlice { 0, 104, 112 } }), BoundOperation(&Operation133, { InputSlice { 1, 112, 120 }, InputSlice { 0, 112, 120 } }), BoundOperation(&Operation133, { InputSlice { 1, 120, 128 }, InputSlice { 0, 120, 128 } }) }, 1),
InstBinding("vminq_s16", {  }, InstSignature { { 128, 128 }, { 128 }, false }, { BoundOperation(&Operation134, { InputSlice { 1, 0, 16 }, InputSlice { 0, 0, 16 } }), BoundOperation(&Operation134, { InputSlice { 1, 16, 32 }, InputSlice { 0, 16, 32 } }), BoundOperation(&Operation134, { InputSlice { 1, 32, 48 }, InputSlice { 0, 32, 48 } }), BoundOperation(&Operation134, { InputSlice { 1, 48, 64 }, InputSlice { 0, 48, 64 } }), BoundOperation(&Operation134, { InputSlice { 1, 64, 80 }, InputSlice { 0, 64, 80 } }), BoundOperation(&Operation134, { InputSlice { 1, 80, 96 }, InputSlice { 0, 80, 96 } }), BoundOperation(&Operation134, { InputSlice { 1, 96, 112 }, InputSlice { 0, 96, 112 } }), BoundOperation(&Operation134, { InputSlice { 1, 112, 128 }, InputSlice { 0, 112, 128 } }) }, 1),
InstBinding("vminq_s32", {  }, InstSignature { { 128, 128 }, { 128 }, false }, { BoundOperation(&Operation135, { InputSlice { 1, 0, 32 }, InputSlice { 0, 0, 32 } }), BoundOperation(&Operation135, { InputSlice { 1, 32, 64 }, InputSlice { 0, 32, 64 } }), BoundOperation(&Operation135, { InputSlice { 1, 64, 96 }, InputSlice { 0, 64, 96 } }), BoundOperation(&Operation135, { InputSlice { 1, 96, 128 }, InputSlice { 0, 96, 128 } }) }, 1),
InstBinding("vminq_u8", {  }, InstSignature { { 128, 128 }, { 128 }, false }, { BoundOperation(&Operation136, { InputSlice { 1, 0, 8 }, InputSlice { 0, 0, 8 } }), BoundOperation(&Operation136, { InputSlice { 1, 8, 16 }, InputSlice { 0, 8, 16 } }), BoundOperation(&Operation136, { InputSlice { 1, 16, 24 }, InputSlice { 0, 16, 24 } }), BoundOperation(&Operation136, { InputSlice { 1, 24, 32 }, InputSlice { 0, 24, 32 } }), BoundOperation(&Operation136, { InputSlice { 1, 32, 40 }, InputSlice { 0, 32, 40 } }), BoundOperation(&Operation136, { InputSlice { 1, 40, 48 }, InputSlice { 0, 40, 48 } }), BoundOperation(&Operation136, { InputSlice { 1, 48, 56 }, InputSlice { 0, 48, 56 } }), BoundOperation(&Operation136, { InputSlice { 1, 56, 64 }, InputSlice { 0, 56, 64 } }), BoundOperation(&Operation136, { InputSlice { 1, 64, 72 }, InputSlice { 0, 64, 72 } }), BoundOperation(&Operation136, { InputSlice { 1, 72, 80 }, InputSlice { 0, 72, 80 } }), BoundOperation(&Operation136, { InputSlice { 1, 80, 88 }, InputSlice { 0, 80, 88 } }), BoundOperation(&Operation136, { InputSlice { 1, 88, 96 }, InputSlice { 0, 88, 96 } }), BoundOperation(&Operation136, { InputSlice { 1, 96, 104 }, InputSlice { 0, 96, 104 } }), BoundOperation(&Operation136, { InputSlice { 1, 104, 112 }, InputSlice { 0, 104, 112 } }), BoundOperation(&Operation136, { InputSlice { 1, 112, 120 }, InputSlice { 0, 112, 120 } }), BoundOperation(&Operation136, { InputSlice { 1, 120, 128 }, InputSlice { 0, 120, 128 } }) }, 1),
InstBinding("vminq_u16", {  }, InstSignature { { 128, 128 }, { 128 }, false }, { BoundOperation(&Operation137, { InputSlice { 1, 0, 16 }, InputSlice { 0, 0, 16 } }), BoundOperation(&Operation137, { InputSlice { 1, 16, 32 }, InputSlice { 0, 16, 32 } }), BoundOperation(&Operation137, { InputSlice { 1, 32, 48 }, InputSlice { 0, 32, 48 } }), BoundOperation(&Operation137, { InputSlice { 1, 48, 64 }, InputSlice { 0, 48, 64 } }), BoundOperation(&Operation137, { InputSlice { 1, 64, 80 }, InputSlice { 0, 64, 80 } }), BoundOperation(&Operation137, { InputSlice { 1, 80, 96 }, InputSlice { 0, 80, 96 } }), BoundOperation(&Operation137, { InputSlice { 1, 96, 112 }, InputSlice { 0, 96, 112 } }), BoundOperation(&Operation137, { InputSlice { 1, 112, 128 }, InputSlice { 0, 112, 128 } }) }, 1),
InstBinding("vminq_u32", {  }, InstSignature { { 128, 128 }, { 128 }, false }, { BoundOperation(&Operation138, { InputSlice { 1, 0, 32 }, InputSlice { 0, 0, 32 } }), BoundOperation(&Operation138, { InputSlice { 1, 32, 64 }, InputSlice { 0, 32, 64 } }), BoundOperation(&Operation138, { InputSlice { 1, 64, 96 }, InputSlice { 0, 64, 96 } }), BoundOperation(&Operation138, { InputSlice { 1, 96, 128 }, InputSlice { 0, 96, 128 } }) }, 1),
InstBinding("vminq_f32", {  }, InstSignature { { 128, 128 }, { 128 }, false }, { BoundOperation(&Operation139, { InputSlice { 0, 0, 32 }, InputSlice { 1, 0, 32 } }), BoundOperation(&Operation139, { InputSlice { 0, 32, 64 }, InputSlice { 1, 32, 64 } }), BoundOperation(&Operation139, { InputSlice { 0, 64, 96 }, InputSlice { 1, 64, 96 } }), BoundOperation(&Operation139, { InputSlice { 0, 96, 128 }, InputSlice { 1, 96, 128 } }) }, 1),
InstBinding("vpadd_s8", {  }, InstSignature { { 64, 64 }, { 64 }, false }, { BoundOperation(&Operation140, { InputSlice { 0, 8, 16 }, InputSlice { 0, 0, 8 } }), BoundOperation(&Operation140, { InputSlice { 0, 24, 32 }, InputSlice { 0, 16, 24 } }), BoundOperation(&Operation140, { InputSlice { 0, 40, 48 }, InputSlice { 0, 32, 40 } }), BoundOperation(&Operation140, { InputSlice { 0, 56, 64 }, InputSlice { 0, 48, 56 } }), BoundOperation(&Operation140, { InputSlice { 1, 8, 16 }, InputSlice { 1, 0, 8 } }), BoundOperation(&Operation140, { InputSlice { 1, 24, 32 }, InputSlice { 1, 16, 24 } }), BoundOperation(&Operation140, { InputSlice { 1, 40, 48 }, InputSlice { 1, 32, 40 } }), BoundOperation(&Operation140, { InputSlice { 1, 56, 64 }, InputSlice { 1, 48, 56 } }) }, 1),
InstBinding("vpadd_s16", {  }, InstSignature { { 64, 64 }, { 64 }, false }, { BoundOperation(&Operation141, { InputSlice { 0, 16, 32 }, InputSlice { 0, 0, 16 } }), BoundOperation(&Operation141, { InputSlice { 0, 48, 64 }, InputSlice { 0, 32, 48 } }), BoundOperation(&Operation141, { InputSlice { 1, 16, 32 }, InputSlice { 1, 0, 16 } }), BoundOperation(&Operation141, { InputSlice { 1, 48, 64 }, InputSlice { 1, 32, 48 } }) }, 1),
InstBinding("vpadd_s32", {  }, InstSignature { { 64, 64 }, { 64 }, false }, { BoundOperation(&Operation142, { InputSlice { 0, 32, 64 }, InputSlice { 0, 0, 32 } }), BoundOperation(&Operation142, { InputSlice { 1, 32, 64 }, InputSlice { 1, 0, 32 } }) }, 1),
InstBinding("vpadd_u8", {  }, InstSignature { { 64, 64 }, { 64 }, false }, { BoundOperation(&Operation140, { InputSlice { 0, 8, 16 }, InputSlice { 0, 0, 8 } }), BoundOperation(&Operation140, { InputSlice { 0, 24, 32 }, InputSlice { 0, 16, 24 } }), BoundOperation(&Operation140, { InputSlice { 0, 40, 48 }, InputSlice { 0, 32, 40 } }), BoundOperation(&Operation140, { InputSlice { 0, 56, 64 }, InputSlice { 0, 48, 56 } }), BoundOperation(&Operation140, { InputSlice { 1, 8, 16 }, InputSlice { 1, 0, 8 } }), BoundOperation(&Operation140, { InputSlice { 1, 24, 32 }, InputSlice { 1, 16, 24 } }), BoundOperation(&Operation140, { InputSlice { 1, 40, 48 }, InputSlice { 1, 32, 40 } }), BoundOperation(&Operation140, { InputSlice { 1, 56, 64 }, InputSlice { 1, 48, 56 } }) }, 1),
InstBinding("vpadd_u16", {  }, InstSignature { { 64, 64 }, { 64 }, false }, { BoundOperation(&Operation141, { InputSlice { 0, 16, 32 }, InputSlice { 0, 0, 16 } }), BoundOperation(&Operation141, { InputSlice { 0, 48, 64 }, InputSlice { 0, 32, 48 } }), BoundOperation(&Operation141, { InputSlice { 1, 16, 32 }, InputSlice { 1, 0, 16 } }), BoundOperation(&Operation141, { InputSlice { 1, 48, 64 }, InputSlice { 1, 32, 48 } }) }, 1),
InstBinding("vpadd_u32", {  }, InstSignature { { 64, 64 }, { 64 }, false }, { BoundOperation(&Operation142, { InputSlice { 0, 32, 64 }, InputSlice { 0, 0, 32 } }), BoundOperation(&Operation142, { InputSlice { 1, 32, 64 }, InputSlice { 1, 0, 32 } }) }, 1),
InstBinding("vpadd_f32", {  }, InstSignature { { 64, 64 }, { 64 }, false }, { BoundOperation(&Operation143, { InputSlice { 0, 0, 32 }, InputSlice { 0, 32, 64 } }), BoundOperation(&Operation143, { InputSlice { 1, 0, 32 }, InputSlice { 1, 32, 64 } }) }, 1),
InstBinding("vpaddl_s8", {  }, InstSignature { { 64 }, { 64 }, false }, { BoundOperation(&Operation0, { InputSlice { 0, 8, 16 }, InputSlice { 0, 0, 8 } }), BoundOperation(&Operation0, { InputSlice { 0, 24, 32 }, InputSlice { 0, 16, 24 } }), BoundOperation(&Operation0, { InputSlice { 0, 40, 48 }, InputSlice { 0, 32, 40 } }), BoundOperation(&Operation0, { InputSlice { 0, 56, 64 }, InputSlice { 0, 48, 56 } }) }, 1),
InstBinding("vpaddl_s16", {  }, InstSignature { { 64 }, { 64 }, false }, { BoundOperation(&Operation1, { InputSlice { 0, 16, 32 }, InputSlice { 0, 0, 16 } }), BoundOperation(&Operation1, { InputSlice { 0, 48, 64 }, InputSlice { 0, 32, 48 } }) }, 1),
InstBinding("vpaddl_s32", {  }, InstSignature { { 64 }, { 64 }, false }, { BoundOperation(&Operation2, { InputSlice { 0, 32, 64 }, InputSlice { 0, 0, 32 } }) }, 1),
InstBinding("vpaddl_u8", {  }, InstSignature { { 64 }, { 64 }, false }, { BoundOperation(&Operation3, { InputSlice { 0, 8, 16 }, InputSlice { 0, 0, 8 } }), BoundOperation(&Operation3, { InputSlice { 0, 24, 32 }, InputSlice { 0, 16, 24 } }), BoundOperation(&Operation3, { InputSlice { 0, 40, 48 }, InputSlice { 0, 32, 40 } }), BoundOperation(&Operation3, { InputSlice { 0, 56, 64 }, InputSlice { 0, 48, 56 } }) }, 1),
InstBinding("vpaddl_u16", {  }, InstSignature { { 64 }, { 64 }, false }, { BoundOperation(&Operation4, { InputSlice { 0, 16, 32 }, InputSlice { 0, 0, 16 } }), BoundOperation(&Operation4, { InputSlice { 0, 48, 64 }, InputSlice { 0, 32, 48 } }) }, 1),
InstBinding("vpaddl_u32", {  }, InstSignature { { 64 }, { 64 }, false }, { BoundOperation(&Operation5, { InputSlice { 0, 32, 64 }, InputSlice { 0, 0, 32 } }) }, 1),
InstBinding("vpaddlq_s8", {  }, InstSignature { { 128 }, { 128 }, false }, { BoundOperation(&Operation0, { InputSlice { 0, 8, 16 }, InputSlice { 0, 0, 8 } }), BoundOperation(&Operation0, { InputSlice { 0, 24, 32 }, InputSlice { 0, 16, 24 } }), BoundOperation(&Operation0, { InputSlice { 0, 40, 48 }, InputSlice { 0, 32, 40 } }), BoundOperation(&Operation0, { InputSlice { 0, 56, 64 }, InputSlice { 0, 48, 56 } }), BoundOperation(&Operation0, { InputSlice { 0, 72, 80 }, InputSlice { 0, 64, 72 } }), BoundOperation(&Operation0, { InputSlice { 0, 88, 96 }, InputSlice { 0, 80, 88 } }), BoundOperation(&Operation0, { InputSlice { 0, 104, 112 }, InputSlice { 0, 96, 104 } }), BoundOperation(&Operation0, { InputSlice { 0, 120, 128 }, InputSlice { 0, 112, 120 } }) }, 1),
InstBinding("vpaddlq_s16", {  }, InstSignature { { 128 }, { 128 }, false }, { BoundOperation(&Operation1, { InputSlice { 0, 16, 32 }, InputSlice { 0, 0, 16 } }), BoundOperation(&Operation1, { InputSlice { 0, 48, 64 }, InputSlice { 0, 32, 48 } }), BoundOperation(&Operation1, { InputSlice { 0, 80, 96 }, InputSlice { 0, 64, 80 } }), BoundOperation(&Operation1, { InputSlice { 0, 112, 128 }, InputSlice { 0, 96, 112 } }) }, 1),
InstBinding("vpaddlq_s32", {  }, InstSignature { { 128 }, { 128 }, false }, { BoundOperation(&Operation2, { InputSlice { 0, 32, 64 }, InputSlice { 0, 0, 32 } }), BoundOperation(&Operation2, { InputSlice { 0, 96, 128 }, InputSlice { 0, 64, 96 } }) }, 1),
InstBinding("vpaddlq_u8", {  }, InstSignature { { 128 }, { 128 }, false }, { BoundOperation(&Operation3, { InputSlice { 0, 8, 16 }, InputSlice { 0, 0, 8 } }), BoundOperation(&Operation3, { InputSlice { 0, 24, 32 }, InputSlice { 0, 16, 24 } }), BoundOperation(&Operation3, { InputSlice { 0, 40, 48 }, InputSlice { 0, 32, 40 } }), BoundOperation(&Operation3, { InputSlice { 0, 56, 64 }, InputSlice { 0, 48, 56 } }), BoundOperation(&Operation3, { InputSlice { 0, 72, 80 }, InputSlice { 0, 64, 72 } }), BoundOperation(&Operation3, { InputSlice { 0, 88, 96 }, InputSlice { 0, 80, 88 } }), BoundOperation(&Operation3, { InputSlice { 0, 104, 112 }, InputSlice { 0, 96, 104 } }), BoundOperation(&Operation3, { InputSlice { 0, 120, 128 }, InputSlice { 0, 112, 120 } }) }, 1),
InstBinding("vpaddlq_u16", {  }, InstSignature { { 128 }, { 128 }, false }, { BoundOperation(&Operation4, { InputSlice { 0, 16, 32 }, InputSlice { 0, 0, 16 } }), BoundOperation(&Operation4, { InputSlice { 0, 48, 64 }, InputSlice { 0, 32, 48 } }), BoundOperation(&Operation4, { InputSlice { 0, 80, 96 }, InputSlice { 0, 64, 80 } }), BoundOperation(&Operation4, { InputSlice { 0, 112, 128 }, InputSlice { 0, 96, 112 } }) }, 1),
InstBinding("vpaddlq_u32", {  }, InstSignature { { 128 }, { 128 }, false }, { BoundOperation(&Operation5, { InputSlice { 0, 32, 64 }, InputSlice { 0, 0, 32 } }), BoundOperation(&Operation5, { InputSlice { 0, 96, 128 }, InputSlice { 0, 64, 96 } }) }, 1),
InstBinding("vpadal_s8", {  }, InstSignature { { 64, 64 }, { 64 }, false }, { BoundOperation(&Operation144, { InputSlice { 1, 0, 8 }, InputSlice { 0, 0, 16 }, InputSlice { 1, 8, 16 } }), BoundOperation(&Operation144, { InputSlice { 1, 16, 24 }, InputSlice { 0, 16, 32 }, InputSlice { 1, 24, 32 } }), BoundOperation(&Operation144, { InputSlice { 1, 32, 40 }, InputSlice { 0, 32, 48 }, InputSlice { 1, 40, 48 } }), BoundOperation(&Operation144, { InputSlice { 1, 48, 56 }, InputSlice { 0, 48, 64 }, InputSlice { 1, 56, 64 } }) }, 1),
InstBinding("vpadal_s16", {  }, InstSignature { { 64, 64 }, { 64 }, false }, { BoundOperation(&Operation145, { InputSlice { 1, 0, 16 }, InputSlice { 0, 0, 32 }, InputSlice { 1, 16, 32 } }), BoundOperation(&Operation145, { InputSlice { 1, 32, 48 }, InputSlice { 0, 32, 64 }, InputSlice { 1, 48, 64 } }) }, 1),
InstBinding("vpadal_s32", {  }, InstSignature { { 64, 64 }, { 64 }, false }, { BoundOperation(&Operation146, { InputSlice { 1, 0, 32 }, InputSlice { 0, 0, 64 }, InputSlice { 1, 32, 64 } }) }, 1),
InstBinding("vpadal_u8", {  }, InstSignature { { 64, 64 }, { 64 }, false }, { BoundOperation(&Operation147, { InputSlice { 1, 0, 8 }, InputSlice { 0, 0, 16 }, InputSlice { 1, 8, 16 } }), BoundOperation(&Operation147, { InputSlice { 1, 16, 24 }, InputSlice { 0, 16, 32 }, InputSlice { 1, 24, 32 } }), BoundOperation(&Operation147, { InputSlice { 1, 32, 40 }, InputSlice { 0, 32, 48 }, InputSlice { 1, 40, 48 } }), BoundOperation(&Operation147, { InputSlice { 1, 48, 56 }, InputSlice { 0, 48, 64 }, InputSlice { 1, 56, 64 } }) }, 1),
InstBinding("vpadal_u16", {  }, InstSignature { { 64, 64 }, { 64 }, false }, { BoundOperation(&Operation148, { InputSlice { 1, 0, 16 }, InputSlice { 0, 0, 32 }, InputSlice { 1, 16, 32 } }), BoundOperation(&Operation148, { InputSlice { 1, 32, 48 }, InputSlice { 0, 32, 64 }, InputSlice { 1, 48, 64 } }) }, 1),
InstBinding("vpadal_u32", {  }, InstSignature { { 64, 64 }, { 64 }, false }, { BoundOperation(&Operation149, { InputSlice { 1, 0, 32 }, InputSlice { 0, 0, 64 }, InputSlice { 1, 32, 64 } }) }, 1),
InstBinding("vpadalq_s8", {  }, InstSignature { { 128, 128 }, { 128 }, false }, { BoundOperation(&Operation144, { InputSlice { 1, 0, 8 }, InputSlice { 0, 0, 16 }, InputSlice { 1, 8, 16 } }), BoundOperation(&Operation144, { InputSlice { 1, 16, 24 }, InputSlice { 0, 16, 32 }, InputSlice { 1, 24, 32 } }), BoundOperation(&Operation144, { InputSlice { 1, 32, 40 }, InputSlice { 0, 32, 48 }, InputSlice { 1, 40, 48 } }), BoundOperation(&Operation144, { InputSlice { 1, 48, 56 }, InputSlice { 0, 48, 64 }, InputSlice { 1, 56, 64 } }), BoundOperation(&Operation144, { InputSlice { 1, 64, 72 }, InputSlice { 0, 64, 80 }, InputSlice { 1, 72, 80 } }), BoundOperation(&Operation144, { InputSlice { 1, 80, 88 }, InputSlice { 0, 80, 96 }, InputSlice { 1, 88, 96 } }), BoundOperation(&Operation144, { InputSlice { 1, 96, 104 }, InputSlice { 0, 96, 112 }, InputSlice { 1, 104, 112 } }), BoundOperation(&Operation144, { InputSlice { 1, 112, 120 }, InputSlice { 0, 112, 128 }, InputSlice { 1, 120, 128 } }) }, 1),
InstBinding("vpadalq_s16", {  }, InstSignature { { 128, 128 }, { 128 }, false }, { BoundOperation(&Operation145, { InputSlice { 1, 0, 16 }, InputSlice { 0, 0, 32 }, InputSlice { 1, 16, 32 } }), BoundOperation(&Operation145, { InputSlice { 1, 32, 48 }, InputSlice { 0, 32, 64 }, InputSlice { 1, 48, 64 } }), BoundOperation(&Operation145, { InputSlice { 1, 64, 80 }, InputSlice { 0, 64, 96 }, InputSlice { 1, 80, 96 } }), BoundOperation(&Operation145, { InputSlice { 1, 96, 112 }, InputSlice { 0, 96, 128 }, InputSlice { 1, 112, 128 } }) }, 1),
InstBinding("vpadalq_s32", {  }, InstSignature { { 128, 128 }, { 128 }, false }, { BoundOperation(&Operation146, { InputSlice { 1, 0, 32 }, InputSlice { 0, 0, 64 }, InputSlice { 1, 32, 64 } }), BoundOperation(&Operation146, { InputSlice { 1, 64, 96 }, InputSlice { 0, 64, 128 }, InputSlice { 1, 96, 128 } }) }, 1),
InstBinding("vpadalq_u8", {  }, InstSignature { { 128, 128 }, { 128 }, false }, { BoundOperation(&Operation147, { InputSlice { 1, 0, 8 }, InputSlice { 0, 0, 16 }, InputSlice { 1, 8, 16 } }), BoundOperation(&Operation147, { InputSlice { 1, 16, 24 }, InputSlice { 0, 16, 32 }, InputSlice { 1, 24, 32 } }), BoundOperation(&Operation147, { InputSlice { 1, 32, 40 }, InputSlice { 0, 32, 48 }, InputSlice { 1, 40, 48 } }), BoundOperation(&Operation147, { InputSlice { 1, 48, 56 }, InputSlice { 0, 48, 64 }, InputSlice { 1, 56, 64 } }), BoundOperation(&Operation147, { InputSlice { 1, 64, 72 }, InputSlice { 0, 64, 80 }, InputSlice { 1, 72, 80 } }), BoundOperation(&Operation147, { InputSlice { 1, 80, 88 }, InputSlice { 0, 80, 96 }, InputSlice { 1, 88, 96 } }), BoundOperation(&Operation147, { InputSlice { 1, 96, 104 }, InputSlice { 0, 96, 112 }, InputSlice { 1, 104, 112 } }), BoundOperation(&Operation147, { InputSlice { 1, 112, 120 }, InputSlice { 0, 112, 128 }, InputSlice { 1, 120, 128 } }) }, 1),
InstBinding("vpadalq_u16", {  }, InstSignature { { 128, 128 }, { 128 }, false }, { BoundOperation(&Operation148, { InputSlice { 1, 0, 16 }, InputSlice { 0, 0, 32 }, InputSlice { 1, 16, 32 } }), BoundOperation(&Operation148, { InputSlice { 1, 32, 48 }, InputSlice { 0, 32, 64 }, InputSlice { 1, 48, 64 } }), BoundOperation(&Operation148, { InputSlice { 1, 64, 80 }, InputSlice { 0, 64, 96 }, InputSlice { 1, 80, 96 } }), BoundOperation(&Operation148, { InputSlice { 1, 96, 112 }, InputSlice { 0, 96, 128 }, InputSlice { 1, 112, 128 } }) }, 1),
InstBinding("vpadalq_u32", {  }, InstSignature { { 128, 128 }, { 128 }, false }, { BoundOperation(&Operation149, { InputSlice { 1, 0, 32 }, InputSlice { 0, 0, 64 }, InputSlice { 1, 32, 64 } }), BoundOperation(&Operation149, { InputSlice { 1, 64, 96 }, InputSlice { 0, 64, 128 }, InputSlice { 1, 96, 128 } }) }, 1),
InstBinding("vpmax_s8", {  }, InstSignature { { 64, 64 }, { 64 }, false }, { BoundOperation(&Operation126, { InputSlice { 0, 8, 16 }, InputSlice { 0, 0, 8 } }), BoundOperation(&Operation126, { InputSlice { 0, 24, 32 }, InputSlice { 0, 16, 24 } }), BoundOperation(&Operation126, { InputSlice { 0, 40, 48 }, InputSlice { 0, 32, 40 } }), BoundOperation(&Operation126, { InputSlice { 0, 56, 64 }, InputSlice { 0, 48, 56 } }), BoundOperation(&Operation126, { InputSlice { 1, 8, 16 }, InputSlice { 1, 0, 8 } }), BoundOperation(&Operation126, { InputSlice { 1, 24, 32 }, InputSlice { 1, 16, 24 } }), BoundOperation(&Operation126, { InputSlice { 1, 40, 48 }, InputSlice { 1, 32, 40 } }), BoundOperation(&Operation126, { InputSlice { 1, 56, 64 }, InputSlice { 1, 48, 56 } }) }, 1),
InstBinding("vpmax_s16", {  }, InstSignature { { 64, 64 }, { 64 }, false }, { BoundOperation(&Operation127, { InputSlice { 0, 16, 32 }, InputSlice { 0, 0, 16 } }), BoundOperation(&Operation127, { InputSlice { 0, 48, 64 }, InputSlice { 0, 32, 48 } }), BoundOperation(&Operation127, { InputSlice { 1, 16, 32 }, InputSlice { 1, 0, 16 } }), BoundOperation(&Operation127, { InputSlice { 1, 48, 64 }, InputSlice { 1, 32, 48 } }) }, 1),
InstBinding("vpmax_s32", {  }, InstSignature { { 64, 64 }, { 64 }, false }, { BoundOperation(&Operation128, { InputSlice { 0, 32, 64 }, InputSlice { 0, 0, 32 } }), BoundOperation(&Operation128, { InputSlice { 1, 32, 64 }, InputSlice { 1, 0, 32 } }) }, 1),
InstBinding("vpmax_u8", {  }, InstSignature { { 64, 64 }, { 64 }, false }, { BoundOperation(&Operation129, { InputSlice { 0, 8, 16 }, InputSlice { 0, 0, 8 } }), BoundOperation(&Operation129, { InputSlice { 0, 24, 32 }, InputSlice { 0, 16, 24 } }), BoundOperation(&Operation129, { InputSlice { 0, 40, 48 }, InputSlice { 0, 32, 40 } }), BoundOperation(&Operation129, { InputSlice { 0, 56, 64 }, InputSlice { 0, 48, 56 } }), BoundOperation(&Operation129, { InputSlice { 1, 8, 16 }, InputSlice { 1, 0, 8 } }), BoundOperation(&Operation129, { InputSlice { 1, 24, 32 }, InputSlice { 1, 16, 24 } }), BoundOperation(&Operation129, { InputSlice { 1, 40, 48 }, InputSlice { 1, 32, 40 } }), BoundOperation(&Operation129, { InputSlice { 1, 56, 64 }, InputSlice { 1, 48, 56 } }) }, 1),
InstBinding("vpmax_u16", {  }, InstSignature { { 64, 64 }, { 64 }, false }, { BoundOperation(&Operation130, { InputSlice { 0, 16, 32 }, InputSlice { 0, 0, 16 } }), BoundOperation(&Operation130, { InputSlice { 0, 48, 64 }, InputSlice { 0, 32, 48 } }), BoundOperation(&Operation130, { InputSlice { 1, 16, 32 }, InputSlice { 1, 0, 16 } }), BoundOperation(&Operation130, { InputSlice { 1, 48, 64 }, InputSlice { 1, 32, 48 } }) }, 1),
InstBinding("vpmax_u32", {  }, InstSignature { { 64, 64 }, { 64 }, false }, { BoundOperation(&Operation131, { InputSlice { 0, 32, 64 }, InputSlice { 0, 0, 32 } }), BoundOperation(&Operation131, { InputSlice { 1, 32, 64 }, InputSlice { 1, 0, 32 } }) }, 1),
InstBinding("vpmax_f32", {  }, InstSignature { { 64, 64 }, { 64 }, false }, { BoundOperation(&Operation132, { InputSlice { 0, 0, 32 }, InputSlice { 0, 32, 64 } }), BoundOperation(&Operation132, { InputSlice { 1, 0, 32 }, InputSlice { 1, 32, 64 } }) }, 1),
InstBinding("vpmin_s8", {  }, InstSignature { { 64, 64 }, { 64 }, false }, { BoundOperation(&Operation133, { InputSlice { 0, 8, 16 }, InputSlice { 0, 0, 8 } }), BoundOperation(&Operation133, { InputSlice { 0, 24, 32 }, InputSlice { 0, 16, 24 } }), BoundOperation(&Operation133, { InputSlice { 0, 40, 48 }, InputSlice { 0, 32, 40 } }), BoundOperation(&Operation133, { InputSlice { 0, 56, 64 }, InputSlice { 0, 48, 56 } }), BoundOperation(&Operation133, { InputSlice { 1, 8, 16 }, InputSlice { 1, 0, 8 } }), BoundOperation(&Operation133, { InputSlice { 1, 24, 32 }, InputSlice { 1, 16, 24 } }), BoundOperation(&Operation133, { InputSlice { 1, 40, 48 }, InputSlice { 1, 32, 40 } }), BoundOperation(&Operation133, { InputSlice { 1, 56, 64 }, InputSlice { 1, 48, 56 } }) }, 1),
InstBinding("vpmin_s16", {  }, InstSignature { { 64, 64 }, { 64 }, false }, { BoundOperation(&Operation134, { InputSlice { 0, 16, 32 }, InputSlice { 0, 0, 16 } }), BoundOperation(&Operation134, { InputSlice { 0, 48, 64 }, InputSlice { 0, 32, 48 } }), BoundOperation(&Operation134, { InputSlice { 1, 16, 32 }, InputSlice { 1, 0, 16 } }), BoundOperation(&Operation134, { InputSlice { 1, 48, 64 }, InputSlice { 1, 32, 48 } }) }, 1),
InstBinding("vpmin_s32", {  }, InstSignature { { 64, 64 }, { 64 }, false }, { BoundOperation(&Operation135, { InputSlice { 0, 32, 64 }, InputSlice { 0, 0, 32 } }), BoundOperation(&Operation135, { InputSlice { 1, 32, 64 }, InputSlice { 1, 0, 32 } }) }, 1),
InstBinding("vpmin_u8", {  }, InstSignature { { 64, 64 }, { 64 }, false }, { BoundOperation(&Operation136, { InputSlice { 0, 8, 16 }, InputSlice { 0, 0, 8 } }), BoundOperation(&Operation136, { InputSlice { 0, 24, 32 }, InputSlice { 0, 16, 24 } }), BoundOperation(&Operation136, { InputSlice { 0, 40, 48 }, InputSlice { 0, 32, 40 } }), BoundOperation(&Operation136, { InputSlice { 0, 56, 64 }, InputSlice { 0, 48, 56 } }), BoundOperation(&Operation136, { InputSlice { 1, 8, 16 }, InputSlice { 1, 0, 8 } }), BoundOperation(&Operation136, { InputSlice { 1, 24, 32 }, InputSlice { 1, 16, 24 } }), BoundOperation(&Operation136, { InputSlice { 1, 40, 48 }, InputSlice { 1, 32, 40 } }), BoundOperation(&Operation136, { InputSlice { 1, 56, 64 }, InputSlice { 1, 48, 56 } }) }, 1),
InstBinding("vpmin_u16", {  }, InstSignature { { 64, 64 }, { 64 }, false }, { BoundOperation(&Operation137, { InputSlice { 0, 16, 32 }, InputSlice { 0, 0, 16 } }), BoundOperation(&Operation137, { InputSlice { 0, 48, 64 }, InputSlice { 0, 32, 48 } }), BoundOperation(&Operation137, { InputSlice { 1, 16, 32 }, InputSlice { 1, 0, 16 } }), BoundOperation(&Operation137, { InputSlice { 1, 48, 64 }, InputSlice { 1, 32, 48 } }) }, 1),
InstBinding("vpmin_u32", {  }, InstSignature { { 64, 64 }, { 64 }, false }, { BoundOperation(&Operation138, { InputSlice { 0, 32, 64 }, InputSlice { 0, 0, 32 } }), BoundOperation(&Operation138, { InputSlice { 1, 32, 64 }, InputSlice { 1, 0, 32 } }) }, 1),
InstBinding("vpmin_f32", {  }, InstSignature { { 64, 64 }, { 64 }, false }, { BoundOperation(&Operation139, { InputSlice { 0, 0, 32 }, InputSlice { 0, 32, 64 } }), BoundOperation(&Operation139, { InputSlice { 1, 0, 32 }, InputSlice { 1, 32, 64 } }) }, 1),
InstBinding("vdot_u32", {  }, InstSignature { { 64, 64, 64 }, { 64 }, false }, { BoundOperation(&Operation150, { InputSlice { 2, 0, 8 }, InputSlice { 1, 0, 8 }, InputSlice { 0, 0, 32 }, InputSlice { 2, 8, 16 }, InputSlice { 1, 8, 16 }, InputSlice { 2, 16, 24 }, InputSlice { 1, 16, 24 }, InputSlice { 2, 24, 32 }, InputSlice { 1, 24, 32 } }), BoundOperation(&Operation150, { InputSlice { 2, 32, 40 }, InputSlice { 1, 32, 40 }, InputSlice { 0, 32, 64 }, InputSlice { 2, 40, 48 }, InputSlice { 1, 40, 48 }, InputSlice { 2, 48, 56 }, InputSlice { 1, 48, 56 }, InputSlice { 2, 56, 64 }, InputSlice { 1, 56, 64 } }) }, 1),
InstBinding("vdot_s32", {  }, InstSignature { { 64, 64, 64 }, { 64 }, false }, { BoundOperation(&Operation151, { InputSlice { 2, 0, 8 }, InputSlice { 1, 0, 8 }, InputSlice { 0, 0, 32 }, InputSlice { 2, 8, 16 }, InputSlice { 1, 8, 16 }, InputSlice { 2, 16, 24 }, InputSlice { 1, 16, 24 }, InputSlice { 2, 24, 32 }, InputSlice { 1, 24, 32 } }), BoundOperation(&Operation151, { InputSlice { 2, 32, 40 }, InputSlice { 1, 32, 40 }, InputSlice { 0, 32, 64 }, InputSlice { 2, 40, 48 }, InputSlice { 1, 40, 48 }, InputSlice { 2, 48, 56 }, InputSlice { 1, 48, 56 }, InputSlice { 2, 56, 64 }, InputSlice { 1, 56, 64 } }) }, 1),
InstBinding("vdotq_u32", {  }, InstSignature { { 128, 128, 128 }, { 128 }, false }, { BoundOperation(&Operation150, { InputSlice { 2, 0, 8 }, InputSlice { 1, 0, 8 }, InputSlice { 0, 0, 32 }, InputSlice { 2, 8, 16 }, InputSlice { 1, 8, 16 }, InputSlice { 2, 16, 24 }, InputSlice { 1, 16, 24 }, InputSlice { 2, 24, 32 }, InputSlice { 1, 24, 32 } }), BoundOperation(&Operation150, { InputSlice { 2, 32, 40 }, InputSlice { 1, 32, 40 }, InputSlice { 0, 32, 64 }, InputSlice { 2, 40, 48 }, InputSlice { 1, 40, 48 }, InputSlice { 2, 48, 56 }, InputSlice { 1, 48, 56 }, InputSlice { 2, 56, 64 }, InputSlice { 1, 56, 64 } }), BoundOperation(&Operation150, { InputSlice { 2, 64, 72 }, InputSlice { 1, 64, 72 }, InputSlice { 0, 64, 96 }, InputSlice { 2, 72, 80 }, InputSlice { 1, 72, 80 }, InputSlice { 2, 80, 88 }, InputSlice { 1, 80, 88 }, InputSlice { 2, 88, 96 }, InputSlice { 1, 88, 96 } }), BoundOperation(&Operation150, { InputSlice { 2, 96, 104 }, InputSlice { 1, 96, 104 }, InputSlice { 0, 96, 128 }, InputSlice { 2, 104, 112 }, InputSlice { 1, 104, 112 }, InputSlice { 2, 112, 120 }, InputSlice { 1, 112, 120 }, InputSlice { 2, 120, 128 }, InputSlice { 1, 120, 128 } }) }, 1),
InstBinding("vdotq_s32", {  }, InstSignature { { 128, 128, 128 }, { 128 }, false }, { BoundOperation(&Operation151, { InputSlice { 2, 0, 8 }, InputSlice { 1, 0, 8 }, InputSlice { 0, 0, 32 }, InputSlice { 2, 8, 16 }, InputSlice { 1, 8, 16 }, InputSlice { 2, 16, 24 }, InputSlice { 1, 16, 24 }, InputSlice { 2, 24, 32 }, InputSlice { 1, 24, 32 } }), BoundOperation(&Operation151, { InputSlice { 2, 32, 40 }, InputSlice { 1, 32, 40 }, InputSlice { 0, 32, 64 }, InputSlice { 2, 40, 48 }, InputSlice { 1, 40, 48 }, InputSlice { 2, 48, 56 }, InputSlice { 1, 48, 56 }, InputSlice { 2, 56, 64 }, InputSlice { 1, 56, 64 } }), BoundOperation(&Operation151, { InputSlice { 2, 64, 72 }, InputSlice { 1, 64, 72 }, InputSlice { 0, 64, 96 }, InputSlice { 2, 72, 80 }, InputSlice { 1, 72, 80 }, InputSlice { 2, 80, 88 }, InputSlice { 1, 80, 88 }, InputSlice { 2, 88, 96 }, InputSlice { 1, 88, 96 } }), BoundOperation(&Operation151, { InputSlice { 2, 96, 104 }, InputSlice { 1, 96, 104 }, InputSlice { 0, 96, 128 }, InputSlice { 2, 104, 112 }, InputSlice { 1, 104, 112 }, InputSlice { 2, 112, 120 }, InputSlice { 1, 112, 120 }, InputSlice { 2, 120, 128 }, InputSlice { 1, 120, 128 } }) }, 1),
InstBinding("vusdot_s32", {  }, InstSignature { { 64, 64, 64 }, { 64 }, false }, { BoundOperation(&Operation152, { InputSlice { 2, 0, 8 }, InputSlice { 1, 0, 8 }, InputSlice { 0, 0, 32 }, InputSlice { 2, 8, 16 }, InputSlice { 1, 8, 16 }, InputSlice { 2, 16, 24 }, InputSlice { 1, 16, 24 }, InputSlice { 2, 24, 32 }, InputSlice { 1, 24, 32 } }), BoundOperation(&Operation152, { InputSlice { 2, 32, 40 }, InputSlice { 1, 32, 40 }, InputSlice { 0, 32, 64 }, InputSlice { 2, 40, 48 }, InputSlice { 1, 40, 48 }, InputSlice { 2, 48, 56 }, InputSlice { 1, 48, 56 }, InputSlice { 2, 56, 64 }, InputSlice { 1, 56, 64 } }) }, 1),
InstBinding("vusdotq_s32", {  }, InstSignature { { 128, 128, 128 }, { 128 }, false }, { BoundOperation(&Operation152, { InputSlice { 2, 0, 8 }, InputSlice { 1, 0, 8 }, InputSlice { 0, 0, 32 }, InputSlice { 2, 8, 16 }, InputSlice { 1, 8, 16 }, InputSlice { 2, 16, 24 }, InputSlice { 1, 16, 24 }, InputSlice { 2, 24, 32 }, InputSlice { 1, 24, 32 } }), BoundOperation(&Operation152, { InputSlice { 2, 32, 40 }, InputSlice { 1, 32, 40 }, InputSlice { 0, 32, 64 }, InputSlice { 2, 40, 48 }, InputSlice { 1, 40, 48 }, InputSlice { 2, 48, 56 }, InputSlice { 1, 48, 56 }, InputSlice { 2, 56, 64 }, InputSlice { 1, 56, 64 } }), BoundOperation(&Operation152, { InputSlice { 2, 64, 72 }, InputSlice { 1, 64, 72 }, InputSlice { 0, 64, 96 }, InputSlice { 2, 72, 80 }, InputSlice { 1, 72, 80 }, InputSlice { 2, 80, 88 }, InputSlice { 1, 80, 88 }, InputSlice { 2, 88, 96 }, InputSlice { 1, 88, 96 } }), BoundOperation(&Operation152, { InputSlice { 2, 96, 104 }, InputSlice { 1, 96, 104 }, InputSlice { 0, 96, 128 }, InputSlice { 2, 104, 112 }, InputSlice { 1, 104, 112 }, InputSlice { 2, 112, 120 }, InputSlice { 1, 112, 120 }, InputSlice { 2, 120, 128 }, InputSlice { 1, 120, 128 } }) }, 1),
InstBinding("vmmlaq_s32", {  }, InstSignature { { 128, 128, 128 }, { 128 }, false }, { BoundOperation(&Operation153, { InputSlice { 2, 0, 8 }, InputSlice { 1, 0, 8 }, InputSlice { 0, 0, 32 }, InputSlice { 2, 8, 16 }, InputSlice { 1, 8, 16 }, InputSlice { 2, 16, 24 }, InputSlice { 1, 16, 24 }, InputSlice { 2, 24, 32 }, InputSlice { 1, 24, 32 }, InputSlice { 2, 32, 40 }, InputSlice { 1, 32, 40 }, InputSlice { 2, 40, 48 }, InputSlice { 1, 40, 48 }, InputSlice { 2, 48, 56 }, InputSlice { 1, 48, 56 } }), BoundOperation(&Operation153, { InputSlice { 2, 64, 72 }, InputSlice { 1, 0, 8 }, InputSlice { 0, 32, 64 }, InputSlice { 2, 72, 80 }, InputSlice { 1, 8, 16 }, InputSlice { 2, 80, 88 }, InputSlice { 1, 16, 24 }, InputSlice { 2, 88, 96 }, InputSlice { 1, 24, 32 }, InputSlice { 2, 96, 104 }, InputSlice { 1, 32, 40 }, InputSlice { 2, 104, 112 }, InputSlice { 1, 40, 48 }, InputSlice { 2, 112, 120 }, InputSlice { 1, 48, 56 } }), BoundOperation(&Operation153, { InputSlice { 1, 64, 72 }, InputSlice { 2, 0, 8 }, InputSlice { 0, 64, 96 }, InputSlice { 1, 72, 80 }, InputSlice { 2, 8, 16 }, InputSlice { 1, 80, 88 }, InputSlice { 2, 16, 24 }, InputSlice { 1, 88, 96 }, InputSlice { 2, 24, 32 }, InputSlice { 1, 96, 104 }, InputSlice { 2, 32, 40 }, InputSlice { 1, 104, 112 }, InputSlice { 2, 40, 48 }, InputSlice { 1, 112, 120 }, InputSlice { 2, 48, 56 } }), BoundOperation(&Operation153, { InputSlice { 2, 64, 72 }, InputSlice { 1, 64, 72 }, InputSlice { 0, 96, 128 }, InputSlice { 2, 72, 80 }, InputSlice { 1, 72, 80 }, InputSlice { 2, 80, 88 }, InputSlice { 1, 80, 88 }, InputSlice { 2, 88, 96 }, InputSlice { 1, 88, 96 }, InputSlice { 2, 96, 104 }, InputSlice { 1, 96, 104 }, InputSlice { 2, 104, 112 }, InputSlice { 1, 104, 112 }, InputSlice { 2, 112, 120 }, InputSlice { 1, 112, 120 } }) }, 1),
InstBinding("vmmlaq_u32", {  }, InstSignature { { 128, 128, 128 }, { 128 }, false }, { BoundOperation(&Operation154, { InputSlice { 2, 0, 8 }, InputSlice { 1, 0, 8 }, InputSlice { 0, 0, 32 }, InputSlice { 2, 8, 16 }, InputSlice { 1, 8, 16 }, InputSlice { 2, 16, 24 }, InputSlice { 1, 16, 24 }, InputSlice { 2, 24, 32 }, InputSlice { 1, 24, 32 }, InputSlice { 2, 32, 40 }, InputSlice { 1, 32, 40 }, InputSlice { 2, 40, 48 }, InputSlice { 1, 40, 48 }, InputSlice { 2, 48, 56 }, InputSlice { 1, 48, 56 } }), BoundOperation(&Operation154, { InputSlice { 2, 64, 72 }, InputSlice { 1, 0, 8 }, InputSlice { 0, 32, 64 }, InputSlice { 2, 72, 80 }, InputSlice { 1, 8, 16 }, InputSlice { 2, 80, 88 }, InputSlice { 1, 16, 24 }, InputSlice { 2, 88, 96 }, InputSlice { 1, 24, 32 }, InputSlice { 2, 96, 104 }, InputSlice { 1, 32, 40 }, InputSlice { 2, 104, 112 }, InputSlice { 1, 40, 48 }, InputSlice { 2, 112, 120 }, InputSlice { 1, 48, 56 } }), BoundOperation(&Operation154, { InputSlice { 1, 64, 72 }, InputSlice { 2, 0, 8 }, InputSlice { 0, 64, 96 }, InputSlice { 1, 72, 80 }, InputSlice { 2, 8, 16 }, InputSlice { 1, 80, 88 }, InputSlice { 2, 16, 24 }, InputSlice { 1, 88, 96 }, InputSlice { 2, 24, 32 }, InputSlice { 1, 96, 104 }, InputSlice { 2, 32, 40 }, InputSlice { 1, 104, 112 }, InputSlice { 2, 40, 48 }, InputSlice { 1, 112, 120 }, InputSlice { 2, 48, 56 } }), BoundOperation(&Operation154, { InputSlice { 2, 64, 72 }, InputSlice { 1, 64, 72 }, InputSlice { 0, 96, 128 }, InputSlice { 2, 72, 80 }, InputSlice { 1, 72, 80 }, InputSlice { 2, 80, 88 }, InputSlice { 1, 80, 88 }, InputSlice { 2, 88, 96 }, InputSlice { 1, 88, 96 }, InputSlice { 2, 96, 104 }, InputSlice { 1, 96, 104 }, InputSlice { 2, 104, 112 }, InputSlice { 1, 104, 112 }, InputSlice { 2, 112, 120 }, InputSlice { 1, 112, 120 } }) }, 1),
InstBinding("vusmmlaq_s32", {  }, InstSignature { { 128, 128, 128 }, { 128 }, false }, { BoundOperation(&Operation155, { InputSlice { 2, 0, 8 }, InputSlice { 1, 0, 8 }, InputSlice { 0, 0, 32 }, InputSlice { 2, 8, 16 }, InputSlice { 1, 8, 16 }, InputSlice { 2, 16, 24 }, InputSlice { 1, 16, 24 }, InputSlice { 2, 24, 32 }, InputSlice { 1, 24, 32 }, InputSlice { 2, 32, 40 }, InputSlice { 1, 32, 40 }, InputSlice { 2, 40, 48 }, InputSlice { 1, 40, 48 }, InputSlice { 2, 48, 56 }, InputSlice { 1, 48, 56 } }), BoundOperation(&Operation155, { InputSlice { 2, 64, 72 }, InputSlice { 1, 0, 8 }, InputSlice { 0, 32, 64 }, InputSlice { 2, 72, 80 }, InputSlice { 1, 8, 16 }, InputSlice { 2, 80, 88 }, InputSlice { 1, 16, 24 }, InputSlice { 2, 88, 96 }, InputSlice { 1, 24, 32 }, InputSlice { 2, 96, 104 }, InputSlice { 1, 32, 40 }, InputSlice { 2, 104, 112 }, InputSlice { 1, 40, 48 }, InputSlice { 2, 112, 120 }, InputSlice { 1, 48, 56 } }), BoundOperation(&Operation155, { InputSlice { 2, 0, 8 }, InputSlice { 1, 64, 72 }, InputSlice { 0, 64, 96 }, InputSlice { 2, 8, 16 }, InputSlice { 1, 72, 80 }, InputSlice { 2, 16, 24 }, InputSlice { 1, 80, 88 }, InputSlice { 2, 24, 32 }, InputSlice { 1, 88, 96 }, InputSlice { 2, 32, 40 }, InputSlice { 1, 96, 104 }, InputSlice { 2, 40, 48 }, InputSlice { 1, 104, 112 }, InputSlice { 2, 48, 56 }, InputSlice { 1, 112, 120 } }), BoundOperation(&Operation155, { InputSlice { 2, 64, 72 }, InputSlice { 1, 64, 72 }, InputSlice { 0, 96, 128 }, InputSlice { 2, 72, 80 }, InputSlice { 1, 72, 80 }, InputSlice { 2, 80, 88 }, InputSlice { 1, 80, 88 }, InputSlice { 2, 88, 96 }, InputSlice { 1, 88, 96 }, InputSlice { 2, 96, 104 }, InputSlice { 1, 96, 104 }, InputSlice { 2, 104, 112 }, InputSlice { 1, 104, 112 }, InputSlice { 2, 112, 120 }, InputSlice { 1, 112, 120 } }) }, 1)
};
  