/*
 *  Copyright 2023 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.xsts.analysis.autoexpl;

import hu.bme.mit.theta.analysis.expr.refinement.autoexpl.AutoExpl;
import hu.bme.mit.theta.analysis.expr.refinement.autoexpl.NewAtomsAutoExpl;
import hu.bme.mit.theta.common.container.Containers;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.StmtAtomCollector;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.xsts.XSTS;

import java.util.Set;
import java.util.stream.Collectors;

public class XstsNewAtomsAutoExpl implements XstsAutoExpl {

    @Override
    public AutoExpl create(XSTS xsts) {
        final Set<Expr<BoolType>> atoms = Containers.createSet();
        atoms.addAll(StmtAtomCollector.collectAtoms(xsts.getEnv()));
        atoms.addAll(StmtAtomCollector.collectAtoms(xsts.getInit()));
        atoms.addAll(StmtAtomCollector.collectAtoms(xsts.getTran()));
        atoms.addAll(ExprUtils.getAtoms(xsts.getProp()));
        atoms.addAll(ExprUtils.getAtoms(xsts.getInitFormula()));

        final Set<Expr<BoolType>> canonicalAtoms = atoms.stream()
                .map(ExprUtils::canonize)
                .flatMap(atom -> ExprUtils.getAtoms(atom).stream())
                .collect(Collectors.toSet());
        return new NewAtomsAutoExpl(xsts.getCtrlVars(), canonicalAtoms, 0);
    }
}
