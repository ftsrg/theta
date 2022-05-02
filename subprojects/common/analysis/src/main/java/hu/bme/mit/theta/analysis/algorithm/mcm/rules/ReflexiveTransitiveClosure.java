/*
 *  Copyright 2022 Budapest University of Technology and Economics
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

package hu.bme.mit.theta.analysis.algorithm.mcm.rules;

import hu.bme.mit.theta.analysis.algorithm.mcm.EncodedRelationWrapper;
import hu.bme.mit.theta.analysis.algorithm.mcm.EventConstantLookup;
import hu.bme.mit.theta.analysis.algorithm.mcm.MCMRelation;
import hu.bme.mit.theta.common.TupleN;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;

import java.util.ArrayList;
import java.util.List;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.*;

public class ReflexiveTransitiveClosure extends UnaryMCMRule{
    public ReflexiveTransitiveClosure(MCMRelation e) {
        super(e);
    }

    @Override
    public String toString() {
        return e.toString() + "*";
    }

    @Override
    public void encodeEvents(List<Integer> idList, EventConstantLookup resultEvents, EncodedRelationWrapper encodedRelationWrapper) {
        final EventConstantLookup events = e.encodeEvents(idList, encodedRelationWrapper);
        resultEvents.getAll().forEach((tuple, constDecl) -> {
            if(tuple.get(0) == tuple.get(1)) encodedRelationWrapper.getSolver().add(constDecl.getRef());
            else {
                int i = tuple.get(0);
                int j = tuple.get(1);
                final List<Expr<BoolType>> subexprs = new ArrayList<>();
                for (final int k : idList) {
                    subexprs.add(And(resultEvents.get(TupleN.of(i, k)).getRef(), events.get(TupleN.of(k, j)).getRef()));
                    subexprs.add(And(resultEvents.get(TupleN.of(k, j)).getRef(), events.get(TupleN.of(i, k)).getRef()));
                }
                subexprs.add(events.get(tuple).getRef());
                encodedRelationWrapper.getSolver().add(Iff(Or(subexprs), constDecl.getRef()));
            }
        });
    }
}
