/*
 *  Copyright 2025 Budapest University of Technology and Economics
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */
package hu.bme.mit.theta.core.decl;

import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.anytype.RefExpr;

public class IndexedVarDecl<DeclType extends Type> extends VarDecl<DeclType> {

    private final VarDecl<DeclType> original;
    private final ConstDecl<DeclType> constDecl;
    private final RefExpr<DeclType> constRef;

    IndexedVarDecl(final String name, final VarDecl<DeclType> original) {
        super(name, original.getType());
        this.original = original;
        this.constDecl = Decls.Const(name, original.getType());
        this.constRef = RefExpr.of(constDecl);
    }

    public static <DeclType extends Type> IndexedVarDecl<DeclType> of(
            final String name, final VarDecl<DeclType> original) {
        return new IndexedVarDecl<>(name, original);
    }

    public VarDecl<DeclType> getOriginal() {
        return original;
    }

    public RefExpr<DeclType> getConstRef() {
        return constRef;
    }

    public ConstDecl<DeclType> getConst() {
        return constDecl;
    }
}
