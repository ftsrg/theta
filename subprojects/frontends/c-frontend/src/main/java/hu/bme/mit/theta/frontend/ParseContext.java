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
package hu.bme.mit.theta.frontend;

import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig.ArchitectureType;
import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig.ArithmeticType;
import hu.bme.mit.theta.frontend.transformation.CStmtCounter;
import hu.bme.mit.theta.frontend.transformation.grammar.preprocess.ArithmeticTrait;
import java.math.BigInteger;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

public class ParseContext {
    private final FrontendMetadata metadata;
    private final CStmtCounter cStmtCounter;
    private Set<ArithmeticTrait> arithmeticTraits = new LinkedHashSet<>();
    private ArchitectureType architecture = ArchitectureType.LP64;
    private Boolean multiThreading = false;
    private ArithmeticType arithmetic = ArithmeticType.efficient;
    private Boolean signedWraparound = false;

    // Which cells of a memory object (keyed by its compile-time base id) are `_Atomic`, so that the
    // data-race check can exclude accesses to them. `_Atomic` is a property of the accessed *cell* --
    // a struct field, an array element, or what a pointer points at -- not of the pointer expression
    // that reaches it, and that expression is a bare base-id literal by the time the analysis runs
    // (folded constants, rebuilt exprs, identity-keyed C types all lost). The base id survives by
    // value, so atomicity is recorded against it where the id is minted (global object layout in the
    // frontend builder, address-taken objects in ReferenceElimination) and looked up by value here.
    private final Set<BigInteger> fullyAtomicObjects = new LinkedHashSet<>();
    private final Map<BigInteger, Set<Integer>> atomicObjectCells = new LinkedHashMap<>();

    // A struct-typed field is a subobject with a base id of its own, kept in the parent's cell. So a
    // nested access `s.i.f` reaches the atomic cell through `(deref (deref parent i) f)`: the inner
    // dereference yields the subobject's base. This maps (parent base, field offset) -> subobject
    // base so the race check can follow that chain to the object the atomicity is recorded against.
    private final Map<BigInteger, Map<Integer, BigInteger>> subObjectCells = new LinkedHashMap<>();

    public ParseContext() {
        metadata = new FrontendMetadata();
        cStmtCounter = new CStmtCounter();
    }

    public ParseContext(
            final FrontendMetadata metadata,
            final CStmtCounter cStmtCounter,
            final Set<ArithmeticTrait> arithmeticTraits,
            final ArchitectureType architecture,
            final Boolean multiThreading,
            final ArithmeticType arithmetic,
            final Boolean signedWraparound) {
        this.metadata = metadata;
        this.cStmtCounter = cStmtCounter;
        this.arithmeticTraits = arithmeticTraits;
        this.architecture = architecture;
        this.multiThreading = multiThreading;
        this.arithmetic = arithmetic;
        this.signedWraparound = signedWraparound;
    }

    public FrontendMetadata getMetadata() {
        return metadata;
    }

    public Set<ArithmeticTrait> getArithmeticTraits() {
        return Set.copyOf(arithmeticTraits);
    }

    public void addArithmeticTrait(ArithmeticTrait arithmeticTrait) {
        this.arithmeticTraits.add(arithmeticTrait);
    }

    public ArchitectureType getArchitecture() {
        return architecture;
    }

    public void setArchitecture(ArchitectureType architecture) {
        this.architecture = architecture;
    }

    public Boolean getMultiThreading() {
        return multiThreading;
    }

    public void setMultiThreading(Boolean multiThreading) {
        this.multiThreading = multiThreading;
    }

    public ArithmeticType getArithmetic() {
        return arithmetic;
    }

    public void setArithmetic(ArithmeticType arithmetic) {
        this.arithmetic = arithmetic;
    }

    public Boolean getSignedWraparound() {
        return signedWraparound;
    }

    public void setSignedWraparound(Boolean signedWraparound) {
        this.signedWraparound = signedWraparound;
    }

    public CStmtCounter getCStmtCounter() {
        return cStmtCounter;
    }

    /** Records that every cell of the object at base id [base] is `_Atomic`. */
    public void markObjectFullyAtomic(BigInteger base) {
        fullyAtomicObjects.add(base);
        atomicObjectCells.remove(base); // fully-atomic subsumes any per-cell record
    }

    /** Records that the cell at unit offset [unitOffset] within object [base] is `_Atomic`. */
    public void markObjectAtomicCell(BigInteger base, int unitOffset) {
        if (fullyAtomicObjects.contains(base)) {
            return;
        }
        atomicObjectCells.computeIfAbsent(base, k -> new LinkedHashSet<>()).add(unitOffset);
    }

    /**
     * Whether the cell at [unitOffset] (null when the offset is not a compile-time constant) within
     * the object at base id [base] is `_Atomic`. A fully-atomic object answers true for any offset.
     */
    public boolean isAtomicObjectCell(BigInteger base, Integer unitOffset) {
        if (fullyAtomicObjects.contains(base)) {
            return true;
        }
        if (unitOffset == null) {
            return false;
        }
        Set<Integer> offsets = atomicObjectCells.get(base);
        return offsets != null && offsets.contains(unitOffset);
    }

    /** Records that cell [unitOffset] of object [parentBase] holds the base id of subobject [subBase]. */
    public void recordSubObjectCell(BigInteger parentBase, int unitOffset, BigInteger subBase) {
        subObjectCells.computeIfAbsent(parentBase, k -> new LinkedHashMap<>()).put(unitOffset, subBase);
    }

    /**
     * The base id of the subobject held in cell [unitOffset] of object [parentBase], or null when no
     * subobject is recorded there.
     */
    public BigInteger subObjectBaseAt(BigInteger parentBase, Integer unitOffset) {
        if (unitOffset == null) {
            return null;
        }
        Map<Integer, BigInteger> cells = subObjectCells.get(parentBase);
        return cells == null ? null : cells.get(unitOffset);
    }
}
