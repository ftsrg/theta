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
package hu.bme.mit.theta.cfa.analysis;

import com.google.common.collect.ImmutableSet;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.cfa.CFA;
import hu.bme.mit.theta.cfa.analysis.lts.CfaLbeLts;
import hu.bme.mit.theta.cfa.analysis.lts.CfaLts;
import hu.bme.mit.theta.cfa.analysis.lts.CfaSbeLts;
import hu.bme.mit.theta.cfa.dsl.CfaDslManager;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;

import java.io.FileInputStream;
import java.io.IOException;

import hu.bme.mit.theta.common.container.Containers;

import java.util.Set;

public class EncodingTest {

    private CFA cfa;

    private CFA.Loc getLocByName(String name) {
        for (CFA.Loc loc : cfa.getLocs()) {
            if (loc.getName().equals(name)) {
                return loc;
            }
        }
        throw new IllegalArgumentException("Location not found");
    }

    private Set<String> getNextLocs(CfaLts lts, String loc) {
        Set<String> locs = Containers.createSet();
        SS ss = new SS();
        for (var act : lts.getEnabledActionsFor(CfaState.of(getLocByName(loc), ss))) {
            locs.add(act.getTarget().getName());
        }
        return locs;
    }

    private class SS implements ExprState {

        @Override
        public boolean isBottom() {
            return false;
        }

        @Override
        public Expr<BoolType> toExpr() {
            return null;
        }
    }

    @Before
    public void load() throws IOException {
        try (var fis = new FileInputStream("src/test/resources/block-encoding.cfa")) {
            cfa = CfaDslManager.createCfa(fis);
        }
    }

    @Test
    public void testSbe() {
        CfaSbeLts lts = CfaSbeLts.getInstance();
        Assert.assertEquals(ImmutableSet.of("L1"), getNextLocs(lts, "L0"));
        Assert.assertEquals(ImmutableSet.of("L2", "L4"), getNextLocs(lts, "L1"));
        Assert.assertEquals(ImmutableSet.of("L3"), getNextLocs(lts, "L2"));
        Assert.assertEquals(ImmutableSet.of("L4"), getNextLocs(lts, "L3"));
        Assert.assertEquals(ImmutableSet.of("L5"), getNextLocs(lts, "L4"));
        Assert.assertEquals(ImmutableSet.of("L1", "L6"), getNextLocs(lts, "L5"));
        Assert.assertEquals(ImmutableSet.of("L7"), getNextLocs(lts, "L6"));
        Assert.assertEquals(ImmutableSet.of(), getNextLocs(lts, "L7"));
    }

    @Test
    public void testLbe1() {
        CfaLbeLts lts = CfaLbeLts.of(getLocByName("L7"));
        Assert.assertEquals(ImmutableSet.of("L1"), getNextLocs(lts, "L0"));
        Assert.assertEquals(ImmutableSet.of("L4"), getNextLocs(lts, "L1"));
        Assert.assertEquals(ImmutableSet.of("L4"), getNextLocs(lts, "L2"));
        Assert.assertEquals(ImmutableSet.of("L4"), getNextLocs(lts, "L3"));
        Assert.assertEquals(ImmutableSet.of("L5"), getNextLocs(lts, "L4"));
        Assert.assertEquals(ImmutableSet.of("L1", "L7"), getNextLocs(lts, "L5"));
        Assert.assertEquals(ImmutableSet.of("L7"), getNextLocs(lts, "L6"));
        Assert.assertEquals(ImmutableSet.of(), getNextLocs(lts, "L7"));
    }

    @Test
    public void testLbe2() {
        CfaLbeLts lts = CfaLbeLts.of(getLocByName("L3"));
        Assert.assertEquals(ImmutableSet.of("L1"), getNextLocs(lts, "L0"));
        Assert.assertEquals(ImmutableSet.of("L3", "L4"), getNextLocs(lts, "L1"));
        Assert.assertEquals(ImmutableSet.of("L3"), getNextLocs(lts, "L2"));
        Assert.assertEquals(ImmutableSet.of("L4"), getNextLocs(lts, "L3"));
        Assert.assertEquals(ImmutableSet.of("L5"), getNextLocs(lts, "L4"));
        Assert.assertEquals(ImmutableSet.of("L1", "L7"), getNextLocs(lts, "L5"));
        Assert.assertEquals(ImmutableSet.of("L7"), getNextLocs(lts, "L6"));
        Assert.assertEquals(ImmutableSet.of(), getNextLocs(lts, "L7"));
    }
}
