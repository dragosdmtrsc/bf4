/*
Copyright 2013-present Barefoot Networks, Inc.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
*/

#ifndef _COMMON_RESOLVEREFERENCES_RESOLVEREFERENCES_H_
#define _COMMON_RESOLVEREFERENCES_RESOLVEREFERENCES_H_

#include "ir/ir.h"
#include "referenceMap.h"
#include "lib/exceptions.h"
#include "lib/cstring.h"

namespace P4 {

class ResolutionContext;
/** Inspector that computes `refMap`: a map from paths to declarations.
 *
 * @pre: None
 *
 * @post: produces an up-to-date `refMap`
 *
 * @todo: is @p rootNamespace redundant, since @p context always has it?
 */
class ResolveReferences : public Inspector {
    /// Reference map -- essentially from paths to declarations.
    ReferenceMap* refMap;

    /// Helper data structure that maintains current context.
    ResolutionContext* context;

    /// The program's root namespace.
    const IR::INamespace* rootNamespace;

    /// Tracks whether forward references are permitted in a context.
    std::vector<bool> resolveForward;

    /// Indicates if _all_ forward references are allowed
    bool anyOrder;

    /// If @true, then warn if one declaration shadows another.
    bool checkShadow;

  protected:
    /// Add namespace @p ns to `context`
    void addToContext(const IR::INamespace* ns);

    /// Remove namespace @p ns from `context`
    void removeFromContext(const IR::INamespace* ns);

    /// Add namespace @p ns to `globals`
    void addToGlobals(const IR::INamespace* ns);

    /// Resolve @p path; if @p isType is `true` then resolution will
    /// only return type nodes.
    void resolvePath(const IR::Path* path, bool isType) const;

 public:
    explicit ResolveReferences(/* out */ P4::ReferenceMap* refMap,
                               bool checkShadow = false);

    Visitor::profile_t init_apply(const IR::Node* node) override;
    void end_apply(const IR::Node* node) override;
    using Inspector::preorder;
    using Inspector::postorder;

    bool preorder(const IR::Type_Name* type) override;
    bool preorder(const IR::PathExpression* path) override;
    bool preorder(const IR::This* pointer) override;
    bool preorder(const IR::Declaration_Instance *decl) override;

#define DECLARE(TYPE)                           \
    bool preorder(const IR::TYPE* t) override;  \
    void postorder(const IR::TYPE* t) override; \

    DECLARE(P4PackageModel)
    DECLARE(P4Program)
    DECLARE(P4Control)
    DECLARE(P4Parser)
    DECLARE(P4Action)
    DECLARE(Function)
    DECLARE(TableProperties)
    DECLARE(Type_Method)
    DECLARE(ParserState)
    DECLARE(Type_Extern)
    DECLARE(Type_ArchBlock)
    DECLARE(Type_StructLike)
    DECLARE(BlockStatement)
#undef DECLARE

    bool preorder(const IR::MethodCallExpression* mce) override;
    bool preorder(const IR::P4Table* table) override;
    bool preorder(const IR::Declaration_MatchKind* d) override;
    bool preorder(const IR::Declaration* d) override
    { refMap->usedName(d->getName().name); return true; }
    bool preorder(const IR::Type_Declaration* d) override
    { refMap->usedName(d->getName().name); return true; }

    void checkShadowing(const IR::INamespace*ns) const;
};

}  // namespace P4

#endif /* _COMMON_RESOLVEREFERENCES_RESOLVEREFERENCES_H_ */
