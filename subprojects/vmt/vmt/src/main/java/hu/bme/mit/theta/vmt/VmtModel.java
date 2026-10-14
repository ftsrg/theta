/*
 *  Copyright 2026 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.vmt;

import com.google.common.base.Preconditions;
import java.util.List;
import java.util.Optional;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaManager;

/**
 * A symbolic transition system read from a VMT file. All formulas are JavaSMT terms of {@link
 * #getFormulaManager()}; the transition relation relates {@link VmtStateVar#current()} to {@link
 * VmtStateVar#next()}, and input variables are free in every step.
 */
public final class VmtModel {

    private final FormulaManager fmgr;
    private final List<VmtStateVar> stateVars;
    private final List<Formula> inputVars;
    private final BooleanFormula init;
    private final BooleanFormula trans;
    private final List<VmtProperty> properties;

    public VmtModel(
            FormulaManager fmgr,
            List<VmtStateVar> stateVars,
            List<Formula> inputVars,
            BooleanFormula init,
            BooleanFormula trans,
            List<VmtProperty> properties) {
        this.fmgr = Preconditions.checkNotNull(fmgr);
        this.stateVars = List.copyOf(stateVars);
        this.inputVars = List.copyOf(inputVars);
        this.init = Preconditions.checkNotNull(init);
        this.trans = Preconditions.checkNotNull(trans);
        this.properties = List.copyOf(properties);
    }

    public FormulaManager getFormulaManager() {
        return fmgr;
    }

    public List<VmtStateVar> getStateVars() {
        return stateVars;
    }

    public List<Formula> getInputVars() {
        return inputVars;
    }

    public BooleanFormula getInit() {
        return init;
    }

    public BooleanFormula getTrans() {
        return trans;
    }

    /** The top-level disjuncts of the transition relation; each one is a complete relation. */
    public List<BooleanFormula> getTransSplit() {
        return List.copyOf(fmgr.getBooleanFormulaManager().toDisjunctionArgs(trans, true));
    }

    public List<VmtProperty> getProperties() {
        return properties;
    }

    public List<VmtProperty> getInvariantProperties() {
        return properties.stream().filter(p -> p.kind() == VmtProperty.Kind.INVARIANT).toList();
    }

    public Optional<VmtStateVar> getStateVar(String name) {
        return stateVars.stream().filter(v -> v.name().equals(name)).findFirst();
    }

    @Override
    public String toString() {
        return "VmtModel{stateVars="
                + stateVars.stream().map(VmtStateVar::name).toList()
                + ", inputs="
                + inputVars.size()
                + ", properties="
                + properties.size()
                + "}";
    }
}
