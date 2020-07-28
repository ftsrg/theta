/*
 *  Copyright 2017 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.xcfa.algorithm;

import com.google.common.base.Preconditions;
import hu.bme.mit.theta.core.decl.Decls;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.xcfa.XCFA;
import hu.bme.mit.theta.xcfa.expl.ExplState;
import hu.bme.mit.theta.xcfa.expl.ProcedureData;
import hu.bme.mit.theta.xcfa.expl.StmtTransition;
import hu.bme.mit.theta.xcfa.expl.partialorder.DependencyRelation;
import org.junit.Test;

import java.util.Collection;
import java.util.Collections;
import java.util.List;

public class DependencyTest {

    static class StmtTransitionMock extends StmtTransition {

        private Collection<VarDecl<?>> rw;
        private Collection<VarDecl<?>> w;

        public StmtTransitionMock(XCFA.Process p, Collection<VarDecl<?>> rw, Collection<VarDecl<?>> w) {
            super(p);
            this.rw = rw;
            this.w = w;

            for (VarDecl<?> x : w) {
                Preconditions.checkArgument(rw.contains(x), "W vars is not subset of RW vars");
            }
        }

        @Override
        public void execute(ExplState state) {
            throw new UnsupportedOperationException();
        }

        @Override
        public boolean enabled(ExplState state) {
            throw new UnsupportedOperationException();
        }

        @Override
        public Collection<VarDecl<?>> getRWVars() {
            return rw;
        }

        @Override
        public Collection<VarDecl<?>> getWVars() {
            return w;
        }
    }

    static class TypeMock implements Type {
        private static final TypeMock instance = new TypeMock();
    }

    private XCFA.Process.Procedure createEmptyProcedure() {
        XCFA.Process.Procedure.Builder builder = XCFA.Process.Procedure.builder();
        XCFA.Process.Procedure.Location init = new XCFA.Process.Procedure.Location("L0", Collections.emptyMap());
        XCFA.Process.Procedure.Location finl = new XCFA.Process.Procedure.Location("L0", Collections.emptyMap());
        builder.addLoc(init);
        builder.addLoc(finl);
        builder.setInitLoc(init);
        builder.setFinalLoc(finl);
        return builder.build();
    }

    private XCFA.Process createEmptyProcess() {
        XCFA.Process.Builder builder = XCFA.Process.builder();
        XCFA.Process.Procedure proc = createEmptyProcedure();
        builder.addProcedure(proc);
        builder.setMainProcedure(proc);
        return builder.build();
    }

    private VarDecl<TypeMock> a = Decls.Var("a", TypeMock.instance);
    private VarDecl<TypeMock> b = Decls.Var("b", TypeMock.instance);
    private XCFA.Process p0 = createEmptyProcess();
    private XCFA.Process p1 = createEmptyProcess();

    @Test
    public void testSameProcess() {
        Preconditions.checkState(DependencyRelation.depends(
                new StmtTransitionMock(p0, /*rw*/ List.of(), /*w*/ List.of()),
                new StmtTransitionMock(p0, /*rw*/ List.of(), /*w*/ List.of())
        ));
    }

    @Test
    public void testDifferentProcess() {
        Preconditions.checkState(!DependencyRelation.depends(
                new StmtTransitionMock(p0, /*rw*/ List.of(), /*w*/ List.of()),
                new StmtTransitionMock(p1, /*rw*/ List.of(), /*w*/ List.of())
        ));
    }

    @Test
    public void testRWDependency() {
        Preconditions.checkState(DependencyRelation.depends(
                new StmtTransitionMock(p0, /*rw*/ List.of(a), /*w*/ List.of()),
                new StmtTransitionMock(p1, /*rw*/ List.of(a), /*w*/ List.of(a))
        ));
        Preconditions.checkState(DependencyRelation.depends(
                new StmtTransitionMock(p0, /*rw*/ List.of(a), /*w*/ List.of(a)),
                new StmtTransitionMock(p1, /*rw*/ List.of(a), /*w*/ List.of())
        ));
    }

    @Test
    public void testRRDependency() {
        Preconditions.checkState(!DependencyRelation.depends(
                new StmtTransitionMock(p0, /*rw*/ List.of(a), /*w*/ List.of()),
                new StmtTransitionMock(p1, /*rw*/ List.of(a), /*w*/ List.of())
        ));
    }

    @Test
    public void testDifferentVariableDependency() {
        Preconditions.checkState(!DependencyRelation.depends(
                new StmtTransitionMock(p0, /*rw*/ List.of(a), /*w*/ List.of(a)),
                new StmtTransitionMock(p1, /*rw*/ List.of(b), /*w*/ List.of())
        ));
    }

    @Test
    public void testWWDependency() {
        Preconditions.checkState(DependencyRelation.depends(
                new StmtTransitionMock(p0, /*rw*/ List.of(a), /*w*/ List.of(a)),
                new StmtTransitionMock(p1, /*rw*/ List.of(a), /*w*/ List.of(a))
        ));
    }

    @Test
    public void testLeaveDifferentProcess() {
        Preconditions.checkState(!DependencyRelation.depends(
                new ProcedureData.LeaveTransition(p0, ""),
                new ProcedureData.LeaveTransition(p1, "")
        ));
    }

    @Test
    public void testLeaveSameProcess() {
        Preconditions.checkState(DependencyRelation.depends(
                new ProcedureData.LeaveTransition(p0, ""),
                new ProcedureData.LeaveTransition(p0, "")
        ));
    }

    @Test
    public void testLeaveDependsStmt() {
        Preconditions.checkState(!DependencyRelation.depends(
                new ProcedureData.LeaveTransition(p0, ""),
                new StmtTransitionMock(p1, Collections.emptyList(), Collections.emptyList())
        ));
    }

    @Test
    public void testLeaveDependsStmtSameProcess() {
        Preconditions.checkState(DependencyRelation.depends(
                new ProcedureData.LeaveTransition(p0, ""),
                new StmtTransitionMock(p0, Collections.emptyList(), Collections.emptyList())
        ));
    }
}
