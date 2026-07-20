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
package hu.bme.mit.theta.frontend.transformation.model.declaration;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.frontend.transformation.model.statements.CStatement;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CVoid;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CArray;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CPointer;
import hu.bme.mit.theta.frontend.transformation.model.types.simple.CSimpleType;
import java.util.ArrayList;
import java.util.List;

public class CDeclaration {

    private CSimpleType type;
    private final String name;
    private final List<VarDecl<?>> varDecls;
    private boolean isFunc;
    private boolean isFuncPointer;
    private int derefCounter = 0;
    private final List<CStatement> arrayDimensions = new ArrayList<>();
    private final List<CDeclaration> functionParams = new ArrayList<>();
    private CStatement initExpr;

    /** Bit width for bitfield struct members (`unsigned lo : 4;`); -1 for ordinary members. */
    private int bitfieldWidth = -1;

    public int getBitfieldWidth() {
        return bitfieldWidth;
    }

    public void setBitfieldWidth(int bitfieldWidth) {
        this.bitfieldWidth = bitfieldWidth;
    }

    public CDeclaration(CSimpleType cSimpleType) {
        this.name = checkNotNull(cSimpleType).getAssociatedName();
        this.type = cSimpleType;
        this.derefCounter = cSimpleType.getPointerLevel();
        this.varDecls = new ArrayList<>();
    }

    public CDeclaration(String name) {
        this.name = name;
        this.varDecls = new ArrayList<>();
    }

    public String getName() {
        return name;
    }

    public int getDerefCounter() {
        return derefCounter;
    }

    public void incDerefCounter(int amount) {
        derefCounter += amount;
    }

    /**
     * Stars written in the declarator itself, split by where they bind relative to the array
     * dimensions. The declarator is walked outwards from the identifier, so a star seen while no
     * dimension has been recorded yet sits *inside* the parentheses and binds outside the array
     * (`T (*p)[N]`, a pointer to an array); a star seen after a dimension binds to the element
     * (`T *p[N]`, an array of pointers). Both end up with the same star and dimension counts, so
     * the order they arrived in is the only thing that tells them apart.
     */
    private int pointerAroundArray = 0;

    private int pointerInsideArray = 0;

    public void addArrayDimension(CStatement expr) {
        arrayDimensions.add(expr);
    }

    /** Records [count] stars written in the declarator (not in the declaration specifiers). */
    public void addDeclaratorPointer(int count) {
        if (arrayDimensions.isEmpty()) {
            pointerAroundArray += count;
        } else {
            pointerInsideArray += count;
        }
    }

    public List<CStatement> getArrayDimensions() {
        return arrayDimensions;
    }

    public void addFunctionParam(CDeclaration decl) {
        functionParams.add(decl);
    }

    public List<CDeclaration> getFunctionParams() {
        return functionParams;
    }

    public CSimpleType getType() {
        return type;
    }

    public CComplexType getActualType() {
        CComplexType actualType = type.getActualType();
        if (isFuncPointer || type.isFunctionPointer()) {
            // In `int (*fp)(int)` the star sits inside the declarator, so (unlike `int *p`) it
            // never
            // reaches the type specifier: wrap it here. The pointer holds a function id, which
            // FunctionPointerCallsPass dispatches on.
            CSimpleType pointerType = type.copyOf();
            pointerType.incrementPointer();
            // The pointee of a function pointer is never dereferenced as data, so a
            // `void`-returning
            // one (`void (*f)(void*)`) uses a benign stand-in: CVoid has no value representation.
            CComplexType pointeeType =
                    actualType instanceof CVoid
                            ? CComplexType.getSignedInt(actualType.getParseContext())
                            : actualType;
            CPointer functionPointer =
                    new CPointer(pointerType, pointeeType, actualType.getParseContext());
            functionPointer.setFunctionPointer(true);
            actualType = functionPointer;
        }
        // `T *p[N]`: the star belongs to the element type, so it goes on before the dimensions.
        for (int i = 0; i < pointerInsideArray; i++) {
            CSimpleType simpleType = type.copyOf();
            simpleType.incrementPointer();
            actualType = new CPointer(simpleType, actualType, actualType.getParseContext());
        }
        // The declarator is walked outwards from the identifier, so `int a[3][4]` records [3, 4] --
        // but it means an array of 3 arrays of 4, so the *last* dimension is the innermost one and
        // they have to be applied back to front. (A single dimension is unaffected, and
        // multi-dimensional arrays were rejected outright before, so nothing working changes.)
        for (int i = arrayDimensions.size() - 1; i >= 0; i--) {
            CSimpleType simpleType = type.copyOf();
            simpleType.incrementPointer();
            actualType =
                    new CArray(
                            simpleType,
                            actualType,
                            actualType.getParseContext(),
                            arrayDimensions.get(i)); // some day change this back to arrays, when
            // simple & complex types are better synchronized...
        }
        // `T (*p)[N]`: the star was written inside the parentheses, so it wraps the whole array --
        // p is a pointer *to* an array. Without this the pointer level was dropped and `(*p)[i]`
        // had no array to subscript ("Non-array expression used as array"). A declaration with no
        // dimensions has no declarator star to place here either, so this leaves it untouched.
        for (int i = 0; i < pointerAroundArray && !arrayDimensions.isEmpty(); i++) {
            CSimpleType simpleType = type.copyOf();
            simpleType.incrementPointer();
            actualType = new CPointer(simpleType, actualType, actualType.getParseContext());
        }

        return actualType;
    }

    public void setType(CSimpleType baseType) {
        this.type = baseType;
    }

    public CStatement getInitExpr() {
        return initExpr;
    }

    public void setInitExpr(CStatement initExpr) {
        this.initExpr = initExpr;
    }

    @Override
    public String toString() {
        StringBuilder stringBuilder = new StringBuilder();
        stringBuilder.append(type).append(" ");
        stringBuilder.append("*".repeat(Math.max(0, derefCounter)));
        stringBuilder.append(name == null ? "" : name);
        for (CStatement arrayDimension : arrayDimensions) {
            stringBuilder.append("[]");
        }
        if (isFunc) {
            stringBuilder.append("(");
        }
        for (CDeclaration functionParam : functionParams) {
            stringBuilder.append(functionParam).append(", ");
        }
        if (isFunc) {
            stringBuilder.append(")");
        }
        if (initExpr != null) {
            stringBuilder.append(" = ").append(initExpr);
        }
        return stringBuilder.toString();
    }

    /**
     * True for a function POINTER variable (e.g. `int (*fp)(int)`), which is a variable, not a
     * function. Its value is a function id; calls through it are dispatched over a candidate set.
     */
    public boolean isFuncPointer() {
        return isFuncPointer;
    }

    public void setFuncPointer(boolean funcPointer) {
        isFuncPointer = funcPointer;
    }

    public boolean isFunc() {
        return isFunc;
    }

    public void setFunc(boolean func) {
        isFunc = func;
    }

    public List<VarDecl<?>> getVarDecls() {
        return varDecls;
    }

    public void addVarDecl(VarDecl<?> varDecl) {
        this.varDecls.add(varDecl);
    }
}
