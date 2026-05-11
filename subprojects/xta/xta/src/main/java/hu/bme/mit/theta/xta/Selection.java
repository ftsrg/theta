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

package hu.bme.mit.theta.xta;

import static hu.bme.mit.theta.core.stmt.Stmts.Assume;
import static hu.bme.mit.theta.core.stmt.Stmts.Havoc;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.SequenceStmt;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.inttype.IntType;
import hu.bme.mit.theta.core.type.rangetype.InRangeExpr;
import hu.bme.mit.theta.core.type.rangetype.RangeType;
import hu.bme.mit.theta.core.utils.TypeUtils;
import java.util.List;

public final class Selection {

    private final VarDecl<RangeType> varDecl;

    private Selection(VarDecl<RangeType> varDecl) {
        this.varDecl = varDecl;
    }

    public static Selection create(VarDecl<RangeType> varDecl) {
        return new Selection(varDecl);
    }

    public final VarDecl<RangeType> getVarDecl() {
        return varDecl;
    }

    public final Stmt toStmt() {
        final Expr<IntType> varRef = TypeUtils.cast(varDecl.getRef(), Int());
        final RangeType range = varDecl.getType();
        final InRangeExpr inRange = InRangeExpr.of(varRef, range);
        return SequenceStmt.of(List.of(Havoc(varDecl), Assume(inRange)));
    }

    @Override
    public String toString() {
        return String.format("select %s", varDecl);
    }
}
