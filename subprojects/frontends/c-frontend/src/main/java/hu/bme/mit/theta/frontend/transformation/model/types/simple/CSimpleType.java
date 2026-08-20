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
package hu.bme.mit.theta.frontend.transformation.model.types.simple;

import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType;
import java.util.ArrayList;
import java.util.List;

/**
 * Any received CType instance will either be a NamedType or an Enum (and later a Struct, still
 * under development). The other subclasses are helper classes to provide metadata on the
 * signedness, atomicity, etc. of the type.
 */
public abstract class CSimpleType {
    private int pointerLevel = 0;
    private Boolean signed = null;
    private boolean bool = false;
    private boolean atomic = false;
    private boolean extern = false;
    private boolean typedef = false;
    private boolean isVolatile = false;
    private boolean isShort = false;
    private boolean isLong = false;
    private boolean isLongLong = false;
    private boolean is128 = false;
    private boolean isThreadLocal = false;

    /**
     * According to the grammar, the first declared variable is part of the type (e.g. `int a` will
     * result in a named type `int`, with an associated name `a`)
     */
    private String associatedName = null;

    public int getPointerLevel() {
        return pointerLevel;
    }

    private boolean functionPointer = false;

    /** True when this type is a pointer to a function (e.g. a `typedef int (*h)(int)`). */
    public boolean isFunctionPointer() {
        return functionPointer;
    }

    public void setFunctionPointer(boolean functionPointer) {
        this.functionPointer = functionPointer;
    }

    /**
     * Which pointer levels are atomic, innermost first -- one entry per `*`. `_Atomic` attaches to
     * a *level* of a type, not to a declaration, and the level is what decides what may be raced
     * on: an access *through* `p` touches what `p` points at, so `_Atomic int *p` makes `p[i]`
     * race-free while leaving `p` an ordinary variable, and `int * _Atomic p` is the exact
     * opposite. One boolean per declaration cannot tell those apart.
     */
    private final List<Boolean> atomicPointers = new ArrayList<>();

    /**
     * How many of the pointer levels came from a `*` written in *this* declaration, as opposed to
     * being inherited from the type the specifiers name (a typedef of a pointer, say).
     *
     * <p>The grammar folds the `*` of `int *p` into the declaration specifiers, so by the time a
     * qualifier is applied the type already has a pointer and there is otherwise no way to tell
     * `_Atomic int *p` (the `*` is this declaration's, so `_Atomic` reached only the `int`) from
     * `int_ptr _Atomic p` (the pointer came with the typedef, so `_Atomic` qualifies *it*).
     */
    private int starPointers = 0;

    public void incrementPointer() {
        ++pointerLevel;
        atomicPointers.add(false);
        ++starPointers;
    }

    /** Whether the pointer at this level -- 0 being the innermost -- is itself atomic. */
    public boolean isAtomicPointer(int level) {
        return level < atomicPointers.size() && atomicPointers.get(level);
    }

    /** `int * _Atomic p`: the `_Atomic` sits after a star, so it is that pointer that is atomic. */
    public void markLastPointerAtomic() {
        if (!atomicPointers.isEmpty()) {
            atomicPointers.set(atomicPointers.size() - 1, true);
        } else {
            atomic = true;
        }
    }

    /** `_Atomic(T)`: the whole of T is atomic -- its outermost level, whatever that is. */
    public void markOutermostAtomic() {
        if (pointerLevel > 0) {
            atomicPointers.set(pointerLevel - 1, true);
        } else {
            atomic = true;
        }
        // What `_Atomic(T)` yields is a type in its own right. Any `*` after it belongs to the
        // declarator and wraps *around* it, so nothing here is a star of this declaration's.
        starPointers = 0;
    }

    /**
     * `_Atomic` written among the declaration specifiers, which qualifies the type they name.
     *
     * <p>That type is the base -- what is written before this declaration's own `*`s -- so for
     * `_Atomic int *p` it is the `int`, and for `int_ptr _Atomic p` (a typedef of `int *`) it is
     * the pointer the typedef brought with it.
     */
    public void applyAtomicQualifier() {
        int inheritedPointers = pointerLevel - starPointers;
        if (inheritedPointers > 0) {
            atomicPointers.set(inheritedPointers - 1, true);
        } else {
            atomic = true;
        }
    }

    /**
     * The pointers this type already has came *with* it -- it was named by a typedef -- so none of
     * them is a star of the declaration now being read, and a `_Atomic` there qualifies the
     * outermost of them rather than reaching past them to the scalar underneath.
     */
    public void markPointersInherited() {
        starPointers = 0;
    }

    public CSimpleType apply(List<CSimpleType> newCtypes) {
        CSimpleType acc = this;
        for (CSimpleType newCtype : newCtypes) {
            acc = newCtype.patch(acc);
        }
        return acc;
    }

    // we return the patched csimpletype, which might be mutated
    protected abstract CSimpleType patch(CSimpleType cSimpleType);

    public boolean isBool() {
        return bool;
    }

    public void setBool(boolean bool) {
        if (bool) {
            setSigned(false); // _Bool isn't signed, but signed might be the default value in some
            // cases
        }
        this.bool = bool;
    }

    public boolean isAtomic() {
        return atomic;
    }

    public void setAtomic(boolean atomic) {
        this.atomic = atomic;
    }

    public boolean isExtern() {
        return extern;
    }

    public void setExtern(boolean extern) {
        this.extern = extern;
    }

    public boolean isTypedef() {
        return typedef;
    }

    public void setTypedef(boolean typedef) {
        this.typedef = typedef;
    }

    public boolean isVolatile() {
        return isVolatile;
    }

    public void setVolatile(boolean aVolatile) {
        isVolatile = aVolatile;
    }

    public String getAssociatedName() {
        return associatedName;
    }

    public void setAssociatedName(String associatedName) {
        this.associatedName = associatedName;
    }

    /**
     * Returns the base type of the C type e.g. `int* a` will result in a CType of int pointer but
     * the semantic meaning is that it is an int and the declared variable is of pointer type (this
     * is a shortcoming of the grammar)
     *
     * @return base type
     */
    public CSimpleType getBaseType() {
        throw new UnsupportedOperationException("Not yet implemented!");
    }

    public Boolean isSigned() {
        return signed;
    }

    public void setSigned(Boolean signed) {
        this.signed = signed;
    }

    public boolean isVoid() {
        return false;
    }

    public boolean is128() {
        return is128;
    }

    public void set128(boolean l128) {
        is128 = l128;
    }

    public boolean isLongLong() {
        return isLongLong;
    }

    public void setLongLong(boolean longLong) {
        isLongLong = longLong;
    }

    public boolean isLong() {
        return isLong;
    }

    public void setLong(boolean aLong) {
        isLong = aLong;
    }

    public boolean isShort() {
        return isShort;
    }

    public void setShort(boolean aShort) {
        isShort = aShort;
    }

    public CSimpleType copyOf() {
        throw new UnsupportedOperationException(
                "Abstract base class CSimpleType should not be copied");
    }

    public CComplexType getActualType() {
        throw new UnsupportedOperationException(
                "Abstract base class CSimpleType should not be used");
    }

    protected void setThreadLocal(boolean threadLocal) {
        this.isThreadLocal = threadLocal;
    }

    public boolean isThreadLocal() {
        return isThreadLocal;
    }

    protected void setUpCopy(CSimpleType copy) {
        copy.setAtomic(this.isAtomic());
        copy.setExtern(this.isExtern());
        copy.setTypedef(this.isTypedef());
        copy.setVolatile(this.isVolatile());
        copy.setSigned(this.isSigned());
        copy.setShort(this.isShort());
        copy.setLong(this.isLong());
        copy.setBool(this.isBool());
        copy.setLongLong(this.isLongLong());
        copy.set128(this.is128());
        for (int i = 0; i < this.getPointerLevel(); i++) {
            copy.incrementPointer();
            if (this.isAtomicPointer(i)) {
                copy.markLastPointerAtomic();
            }
        }
        copy.starPointers = this.starPointers; // a copy inherits what the original inherited
        copy.setFunctionPointer(this.isFunctionPointer());
    }
}
