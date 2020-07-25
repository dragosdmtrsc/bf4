//
// Created by dragos on 19.09.2019.
//

#include "ImplementPacket.h"
#include "analysis_helpers.h"

namespace analysis {

class ReplaceMutablePacket : public Transform {
  P4::ReferenceMap *refMap;
  P4::TypeMap *typeMap;

  const IR::Type *contentType() { return new IR::Type_Bits(12, false); }

  const IR::Node *postorder(IR::P4Program *prog) override {
    auto &instance = analysis::AnalysisLibrary::instance;
    auto dec = prog->getDeclsByName(instance.packetModel.name);
    if (dec) {
      auto b = dec->begin();
      if (b != dec->end()) return prog;
    }
    auto strt = new IR::Type_Newtype(instance.packetModel.name,
                                     ImplementPacket::packetType());
    strt->annotations = strt->annotations->addAnnotation("noremove", nullptr);
    //    auto strt = new IR::Type_Struct(prog->srcInfo,
    //    instance.packetModel.name);
    //    strt->fields.push_back(
    //        new IR::StructField(IR::ID(prog->srcInfo, "length"), lenType()));
    //    strt->fields.push_back(
    //        new IR::StructField(IR::ID(prog->srcInfo, "contents"),
    //        contentType()));
    IR::Vector<IR::Node> nobjs;
    nobjs.push_back(strt);
    // make definitions here:
    // out H peek<H>(packet_model);
    {
      auto H = new IR::Type_Var("H");
      auto mt = new IR::Type_Method(
          new IR::TypeParameters({H}), new IR::Type_Name("H"),
          new IR::ParameterList({new IR::Parameter(
              "self", IR::Direction::In,
              new IR::Type_Name(instance.packetModel.name))}));
      nobjs.push_back(
          new IR::Method(prog->srcInfo, instance.packetModel.peek.name, mt));
    }
    // H pop<H>(inout packet_model)
    {
      auto H = new IR::Type_Var("H");
      auto mt = new IR::Type_Method(
          new IR::TypeParameters({H}), new IR::Type_Name("H"),
          new IR::ParameterList({new IR::Parameter(
              "self", IR::Direction::InOut,
              new IR::Type_Name(instance.packetModel.name))}));
      nobjs.push_back(
          new IR::Method(prog->srcInfo, instance.packetModel.pop.name, mt));
    }
    // void advance(inout packet_model, int)
    {
      auto mt = new IR::Type_Method(
          new IR::TypeParameters(), IR::Type_Void::get(),
          new IR::ParameterList(
              {new IR::Parameter("self", IR::Direction::InOut,
                                 new IR::Type_Name(instance.packetModel.name)),
               new IR::Parameter("by", IR::Direction::In,
                                 new IR::Type_InfInt())}));
      nobjs.push_back(
          new IR::Method(prog->srcInfo, instance.packetModel.advance.name, mt));
    }
    // void emit(inout packet_model, in H)
    {
      auto H = new IR::Type_Var("H");
      auto mt = new IR::Type_Method(
          new IR::TypeParameters({H}), IR::Type_Void::get(),
          new IR::ParameterList(
              {new IR::Parameter("self", IR::Direction::InOut,
                                 new IR::Type_Name(instance.packetModel.name)),
               new IR::Parameter("h", IR::Direction::In,
                                 new IR::Type_Name("H"))}));
      nobjs.push_back(
          new IR::Method(prog->srcInfo, instance.packetModel.emit.name, mt));
    }
    // void zero(out packet_model)
    {
      auto mt = new IR::Type_Method(
          new IR::TypeParameters(), IR::Type_Void::get(),
          new IR::ParameterList({new IR::Parameter(
              "self", IR::Direction::Out,
              new IR::Type_Name(instance.packetModel.name))}));
      nobjs.push_back(
          new IR::Method(prog->srcInfo, instance.packetModel.zero.name, mt));
    }
    // void prepend(inout packet_model self, in packet_model other)
    {
      auto mt = new IR::Type_Method(
          new IR::TypeParameters(), IR::Type_Void::get(),
          new IR::ParameterList(
              {new IR::Parameter("self", IR::Direction::InOut,
                                 new IR::Type_Name(instance.packetModel.name)),
               new IR::Parameter(
                   "h", IR::Direction::In,
                   new IR::Type_Name(instance.packetModel.name))}));
      nobjs.push_back(
          new IR::Method(prog->srcInfo, instance.packetModel.prepend.name, mt));
    }
    // void copy(in from, out to)
    {
      auto mt = new IR::Type_Method(
          new IR::TypeParameters(), IR::Type_Void::get(),
          new IR::ParameterList(
              {new IR::Parameter("from", IR::Direction::In,
                                 new IR::Type_Name(instance.packetModel.name)),
               new IR::Parameter(
                   "to", IR::Direction::Out,
                   new IR::Type_Name(instance.packetModel.name))}));
      nobjs.push_back(
          new IR::Method(prog->srcInfo, instance.packetModel.copy.name, mt));
    }

    nobjs.append(prog->objects);
    prog->objects = std::move(nobjs);
    return prog;
  }

  const IR::Node *postorder(IR::Parameter *decl) override {
    auto tp = typeMap->getType(getOriginal());
    if (tp->is<IR::Type_Extern>()) {
      auto textern = tp->to<IR::Type_Extern>();
      if (textern->name ==
          analysis::AnalysisLibrary::instance.mutablePacket.name) {
        decl->type = new IR::Type_Name(
            analysis::AnalysisLibrary::instance.packetModel.name);
        decl->direction =
            (decl->getAnnotation(
                 analysis::AnalysisLibrary::instance.readonly.name) != nullptr)
                ? IR::Direction::In
                : IR::Direction::InOut;
        auto annots = decl->annotations->clone();
        annots->addAnnotation(
            analysis::AnalysisLibrary::instance.mutablePacket.name, nullptr);
        decl->annotations = annots;
      }
    }
    return decl;
  }

  const IR::Statement *advance(const IR::Expression *pack, unsigned by) {
    auto len = new IR::Member(pack, "length");
    auto cts = contents(pack);
    auto declen = new IR::Sub(len, new IR::Constant(by));
    auto shiftright = new IR::Shr(cts, new IR::Constant(by));
    return new IR::BlockStatement(
        {new IR::AssignmentStatement(len, declen),
         new IR::AssignmentStatement(cts, shiftright)});
  }
  unsigned sz(const IR::Type *by) {
    if (auto tb = by->to<IR::Type_Bits>())
      return static_cast<unsigned int>(tb->size);
    BUG("can't advance by %1%, flatten extracts first", by);
  }
  const IR::Statement *advance(const IR::Expression *pack, const IR::Type *by) {
    return advance(pack, sz(by));
  }
  const IR::Expression *contents(const IR::Expression *pack) {
    return new IR::Member(pack, "contents");
  }
  const IR::Expression *len(const IR::Expression *pack) {
    return new IR::Member(pack, "length");
  }
  const IR::Type *lenType() { return new IR::Type_Bits(13, false); }
  const IR::Node *preorder(IR::MethodCallExpression *mce) override {
    auto mi = P4::MethodInstance::resolve(
        getOriginal<IR::MethodCallExpression>(), refMap, typeMap);
    auto &instance = analysis::AnalysisLibrary::instance;
    if (mi->is<P4::ExternMethod>()) {
      auto pack = mi->expr->method->to<IR::Member>()->expr;
      auto em = mi->to<P4::ExternMethod>();
      if (em->actualExternType->name == instance.mutablePacket.name) {
        if (em->method->name == instance.mutablePacket.lookahead.name) {
          auto vargs = new IR::Vector<IR::Argument>();
          vargs->emplace_back(pack);
          prune();
          return new IR::MethodCallExpression(
              new IR::PathExpression(instance.packetModel.peek.name),
              mi->expr->typeArguments, vargs);
        }
      }
    }
    return mce;
  }

  const IR::Node *preorder(IR::MethodCallStatement *mcs) override {
    auto mi = P4::MethodInstance::resolve(
        getOriginal<IR::MethodCallStatement>(), refMap, typeMap);
    auto &instance = analysis::AnalysisLibrary::instance;
    if (mi->is<P4::ExternMethod>()) {
      auto pack = mi->expr->method->to<IR::Member>()->expr;
      auto em = mi->to<P4::ExternMethod>();
      if (em->actualExternType->name == instance.mutablePacket.name) {
        if (em->method->name == instance.mutablePacket.extract.name ||
            em->method->name == instance.mutablePacket.emit.name) {
          auto lv = mi->expr->arguments->at(mi->expr->arguments->size() - 1)
                        ->expression;
          auto lt = typeMap->getType(lv);
          if (em->method->name == instance.mutablePacket.extract.name &&
              mi->expr->arguments->size() == 1) {
            prune();
            auto vargs = new IR::Vector<IR::Argument>();
            vargs->emplace_back(pack);
            auto pk = new IR::AssignmentStatement(
                lv, new IR::MethodCallExpression(
                        new IR::PathExpression(instance.packetModel.pop.name),
                        new IR::Vector<IR::Type>({lt}), vargs));
            return new IR::BlockStatement({pk});
          } else if (em->method->name == instance.mutablePacket.emit.name) {
            prune();
            auto vargs = new IR::Vector<IR::Argument>();
            vargs->emplace_back(pack);
            vargs->append(*mi->expr->arguments);
            return new IR::MethodCallStatement(new IR::MethodCallExpression(
                new IR::PathExpression(instance.packetModel.emit.name), vargs));
          }
        }
      }
    } else if (mi->is<P4::ExternFunction>()) {
      auto ef = mi->to<P4::ExternFunction>();
      if (ef->method->name == instance.emptyPacket.name) {
        prune();
        return new IR::MethodCallStatement(new IR::MethodCallExpression(
            new IR::PathExpression(instance.packetModel.zero.name),
            mi->expr->arguments));
      } else if (ef->method->name == instance.readPacket.name) {
        auto pack = mi->expr->arguments->at(0)->expression;
        prune();
        auto readcontents = new IR::AssignmentStatement(
            pack, new IR::MethodCallExpression(
                      new IR::PathExpression(instance.havoc.name),
                      new IR::Vector<IR::Type>(
                          {new IR::Type_Name(instance.packetModel.name)})));
        return readcontents;
      } else if (ef->method->name == instance.prependPacket.name) {
        prune();
        return new IR::MethodCallStatement(new IR::MethodCallExpression(
            new IR::PathExpression(instance.packetModel.prepend.name),
            mi->expr->arguments));
      } else if (ef->method->name == instance.copyPacket.name) {
        auto self = mi->expr->arguments->at(0)->expression;
        auto other = mi->expr->arguments->at(1)->expression;
        prune();
        auto args = new IR::Vector<IR::Argument>();
        args->emplace_back(other);
        args->emplace_back(self);
        return new IR::AssignmentStatement(self, other);
      }
    }
    return mcs;
  }

  const IR::Node *postorder(IR::Declaration_Instance *decl) override {
    auto tp = typeMap->getType(getOriginal());
    if (tp->is<IR::Type_Extern>()) {
      auto textern = tp->to<IR::Type_Extern>();
      if (textern->name ==
          analysis::AnalysisLibrary::instance.mutablePacket.name) {
        decl->type = new IR::Type_Name("packet_model");
        auto vardec = new IR::Declaration_Variable(
            decl->name, new IR::Type_Name("packet_model"));
        auto annots = vardec->annotations->clone();
        annots->addAnnotation(
            analysis::AnalysisLibrary::instance.mutablePacket.name, nullptr);
        vardec->annotations = annots;
        return vardec;
      }
    }
    return decl;
  }

 public:
  ReplaceMutablePacket(P4::ReferenceMap *refMap, P4::TypeMap *typeMap)
      : refMap(refMap), typeMap(typeMap) {}
};

ImplementPacket::ImplementPacket(P4::ReferenceMap *refMap, P4::TypeMap *typeMap)
    : refMap(refMap), typeMap(typeMap) {
  passes.push_back(new ReplaceMutablePacket(refMap, typeMap));
  addPasses({new P4::ClearTypeMap(typeMap), new P4::ResolveReferences(refMap),
             new P4::TypeInference(refMap, typeMap, false)});
}
}
