/*
 *  Copyright 2024 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.sts.analysis;

import hu.bme.mit.theta.analysis.algorithm.AbstractMonolithicTransFunc;
import hu.bme.mit.theta.analysis.algorithm.MonolithicTransFunc;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.indexings.VarIndexing;
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory;
import hu.bme.mit.theta.solver.SolverFactory;
import hu.bme.mit.theta.sts.STS;

import java.util.Collection;
import java.util.function.Function;

public class StsToMonoliticTransFunc extends AbstractMonolithicTransFunc {
    private StsToMonoliticTransFunc(STS sts) {
        transExpr = sts.getTrans();
        initExpr = sts.getInit();
        propExpr = sts.getProp();
        firstIndex = VarIndexingFactory.indexing(0);
        offsetIndex = VarIndexingFactory.indexing(1);
    }

    public static MonolithicTransFunc create(STS sts) {
        return new StsToMonoliticTransFunc(sts);
    }
}
