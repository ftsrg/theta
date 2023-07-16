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

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.frontend.ParseContext;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CVoid;

import java.util.List;
import java.util.Optional;

import static hu.bme.mit.theta.core.decl.Decls.Var;

public class CCall extends CStatement {

    private final VarDecl<?> ret;
    private final String functionId;
    private final List<CStatement> params;

    public CCall(String functionId, List<CStatement> params, ParseContext parseContext) {
        super(parseContext);
        this.functionId = functionId;
        this.params = params;
        Optional<Object> cTypeOpt = parseContext.getMetadata().getMetadataValue(functionId, "cType");
        CComplexType type = (CComplexType) cTypeOpt.orElseGet(() -> new CVoid(null, parseContext));
        ret = Var("call_" + functionId + "_ret" + counter++, type.getSmtType());
        parseContext.getMetadata().create(ret.getRef(), "cType", type);
    }

    public List<CStatement> getParams() {
        return params;
    }

    public VarDecl<?> getRet() {
        return ret;
    }

    public String getFunctionId() {
        return functionId;
    }

    @Override
    public <P, R> R accept(CStatementVisitor<P, R> visitor, P param) {
        return visitor.visit(this, param);
    }
}
