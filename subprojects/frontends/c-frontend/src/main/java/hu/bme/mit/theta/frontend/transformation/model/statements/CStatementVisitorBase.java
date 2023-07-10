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

package hu.bme.mit.theta.frontend.transformation.model.statements;

public abstract class CStatementVisitorBase<P, R> implements CStatementVisitor<P, R> {

    public R visit(CAssignment statement, P param) {
        throw new UnsupportedOperationException("Not implemented");
    }

    public R visit(CAssume statement, P param) {
        throw new UnsupportedOperationException("Not implemented");
    }

    public R visit(CBreak statement, P param) {
        throw new UnsupportedOperationException("Not implemented");
    }

    public R visit(CCall statement, P param) {
        throw new UnsupportedOperationException("Not implemented");
    }

    public R visit(CCase statement, P param) {
        throw new UnsupportedOperationException("Not implemented");
    }

    public R visit(CCompound statement, P param) {
        throw new UnsupportedOperationException("Not implemented");
    }

    public R visit(CContinue statement, P param) {
        throw new UnsupportedOperationException("Not implemented");
    }

    public R visit(CDecls statement, P param) {
        throw new UnsupportedOperationException("Not implemented");
    }

    public R visit(CDefault statement, P param) {
        throw new UnsupportedOperationException("Not implemented");
    }

    public R visit(CDoWhile statement, P param) {
        throw new UnsupportedOperationException("Not implemented");
    }

    public R visit(CExpr statement, P param) {
        throw new UnsupportedOperationException("Not implemented");
    }

    public R visit(CFor statement, P param) {
        throw new UnsupportedOperationException("Not implemented");
    }

    public R visit(CFunction statement, P param) {
        throw new UnsupportedOperationException("Not implemented");
    }

    public R visit(CGoto statement, P param) {
        throw new UnsupportedOperationException("Not implemented");
    }

    public R visit(CIf statement, P param) {
        throw new UnsupportedOperationException("Not implemented");
    }

    public R visit(CInitializerList statement, P param) {
        throw new UnsupportedOperationException("Not implemented");
    }

    public R visit(CProgram statement, P param) {
        throw new UnsupportedOperationException("Not implemented");
    }

    public R visit(CRet statement, P param) {
        throw new UnsupportedOperationException("Not implemented");
    }

    public R visit(CSwitch statement, P param) {
        throw new UnsupportedOperationException("Not implemented");
    }

    public R visit(CWhile statement, P param) {
        throw new UnsupportedOperationException("Not implemented");
    }
}
