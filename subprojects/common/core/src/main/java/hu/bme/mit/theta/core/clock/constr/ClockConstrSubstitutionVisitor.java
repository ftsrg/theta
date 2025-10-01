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

package hu.bme.mit.theta.core.clock.constr;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.rattype.RatType;

import java.util.Collection;
import java.util.function.Function;

import static hu.bme.mit.theta.core.clock.constr.ClockConstrs.*;

public class ClockConstrSubstitutionVisitor implements ClockConstrVisitor<Function<VarDecl<RatType>, VarDecl<RatType>>, ClockConstr> {

    @Override
    public ClockConstr visit(TrueConstr constr, Function<VarDecl<RatType>, VarDecl<RatType>> substitution) {
        return constr;
    }

    @Override
    public ClockConstr visit(FalseConstr constr, Function<VarDecl<RatType>, VarDecl<RatType>> substitution) {
        return constr;
    }

    @Override
    public ClockConstr visit(UnitLtConstr constr, Function<VarDecl<RatType>, VarDecl<RatType>> substitution) {
        return Lt(
                substitution.apply(constr.getVar()),
                constr.getBound());
    }

    @Override
    public ClockConstr visit(UnitLeqConstr constr, Function<VarDecl<RatType>, VarDecl<RatType>> substitution) {
        return Leq(
                substitution.apply(constr.getVar()),
                constr.getBound());
    }

    @Override
    public ClockConstr visit(UnitGtConstr constr, Function<VarDecl<RatType>, VarDecl<RatType>> substitution) {
        return Gt(
                substitution.apply(constr.getVar()),
                constr.getBound());
    }

    @Override
    public ClockConstr visit(UnitGeqConstr constr, Function<VarDecl<RatType>, VarDecl<RatType>> substitution) {
        return Geq(
                substitution.apply(constr.getVar()),
                constr.getBound());
    }

    @Override
    public ClockConstr visit(UnitEqConstr constr, Function<VarDecl<RatType>, VarDecl<RatType>> substitution) {
        return Eq(
                substitution.apply(constr.getVar()),
                constr.getBound());
    }

    @Override
    public ClockConstr visit(DiffLtConstr constr, Function<VarDecl<RatType>, VarDecl<RatType>> substitution) {
        return Lt(
                substitution.apply(constr.getLeftVar()),
                substitution.apply(constr.getRightVar()),
                constr.getBound());
    }

    @Override
    public ClockConstr visit(DiffLeqConstr constr, Function<VarDecl<RatType>, VarDecl<RatType>> substitution) {
        return Leq(
                substitution.apply(constr.getLeftVar()),
                substitution.apply(constr.getRightVar()),
                constr.getBound());
    }

    @Override
    public ClockConstr visit(DiffGtConstr constr, Function<VarDecl<RatType>, VarDecl<RatType>> substitution) {
        return Gt(
                substitution.apply(constr.getLeftVar()),
                substitution.apply(constr.getRightVar()),
                constr.getBound());
    }

    @Override
    public ClockConstr visit(DiffGeqConstr constr, Function<VarDecl<RatType>, VarDecl<RatType>> substitution) {
        return Geq(
                substitution.apply(constr.getLeftVar()),
                substitution.apply(constr.getRightVar()),
                constr.getBound());
    }

    @Override
    public ClockConstr visit(DiffEqConstr constr, Function<VarDecl<RatType>, VarDecl<RatType>> substitution) {
        return Eq(
                substitution.apply(constr.getLeftVar()),
                substitution.apply(constr.getRightVar()),
                constr.getBound());
    }

    @Override
    public ClockConstr visit(AndConstr andConstr, Function<VarDecl<RatType>, VarDecl<RatType>> substitution) {
        final Collection<ClockConstr> constrs =  andConstr.getConstrs().stream()
                .map(constr -> constr.accept(this, substitution))
                .toList();
        return ClockConstrs.And(constrs);
    }
}
