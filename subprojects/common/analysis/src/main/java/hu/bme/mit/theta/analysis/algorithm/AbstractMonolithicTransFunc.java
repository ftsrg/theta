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
package hu.bme.mit.theta.analysis.algorithm;

import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.indexings.VarIndexing;

public abstract class AbstractMonolithicTransFunc implements MonolithicTransFunc {
    protected Expr<BoolType> transExpr;
    protected Expr<BoolType> initExpr;
    protected VarIndexing firstIndex;
    protected VarIndexing offsetIndex;
    protected Expr<BoolType> propExpr;

    @Override
    public Expr<BoolType> getTransExpr() {
        return transExpr;
    }

    @Override
    public Expr<BoolType> getInitExpr() {
        return initExpr;
    }

    @Override
    public Expr<BoolType> getPropExpr() {
        return propExpr;
    }

    @Override
    public VarIndexing getInitIndexing() {
        return firstIndex;
    }

    @Override
    public VarIndexing getOffsetIndexing() {
        return offsetIndex;
    }
}
