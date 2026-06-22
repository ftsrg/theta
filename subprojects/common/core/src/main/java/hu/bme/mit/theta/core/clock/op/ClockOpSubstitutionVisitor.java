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

package hu.bme.mit.theta.core.clock.op;

import hu.bme.mit.theta.core.clock.constr.ClockConstr;
import hu.bme.mit.theta.core.clock.constr.ClockConstrSubstitutionVisitor;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.rattype.RatType;

import java.util.function.Function;

public class ClockOpSubstitutionVisitor implements ClockOpVisitor<Function<VarDecl<RatType>, VarDecl<RatType>>, ClockOp> {

    @Override
    public ClockOp visit(CopyOp op, Function<VarDecl<RatType>, VarDecl<RatType>> substitution) {
        final VarDecl<RatType> sVar = substitution.apply(op.getVar());
        final VarDecl<RatType> sValue = substitution.apply(op.getValue());
        return ClockOps.Copy(sVar, sValue);
    }

    @Override
    public ClockOp visit(FreeOp op, Function<VarDecl<RatType>, VarDecl<RatType>> substitution) {
        final VarDecl<RatType> sVar = substitution.apply(op.getVar());
        return ClockOps.Free(sVar);
    }

    @Override
    public ClockOp visit(GuardOp op, Function<VarDecl<RatType>, VarDecl<RatType>> substitution) {
        final ClockConstr sConstr = op.getConstr().accept(new ClockConstrSubstitutionVisitor(), substitution);
        return ClockOps.Guard(sConstr);
    }

    @Override
    public ClockOp visit(ResetOp op, Function<VarDecl<RatType>, VarDecl<RatType>> substitution) {
        final VarDecl<RatType> sVar = substitution.apply(op.getVar());
        return ClockOps.Reset(sVar, op.getValue());
    }

    @Override
    public ClockOp visit(ShiftOp op, Function<VarDecl<RatType>, VarDecl<RatType>> substitution) {
        final VarDecl<RatType> sVar = substitution.apply(op.getVar());
        return ClockOps.Shift(sVar, op.getOffset());
    }
}
