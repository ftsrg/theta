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
package hu.bme.mit.theta.frontend.svlib;


import static hu.bme.mit.theta.frontend.svlib.SvLibUtils.unsupported;
import static hu.bme.mit.theta.xcfa.utils.UtilsKt.AssignStmtLabel;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.AssumeStmt;
import hu.bme.mit.theta.core.stmt.HavocStmt;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.svlib.frontend.dsl.gen.SvLibBaseVisitor;
import hu.bme.mit.theta.svlib.frontend.dsl.gen.SvLibParser;
import hu.bme.mit.theta.xcfa.model.EmptyMetaData;
import hu.bme.mit.theta.xcfa.model.NopLabel;
import hu.bme.mit.theta.xcfa.model.SequenceLabel;
import hu.bme.mit.theta.xcfa.model.StmtLabel;
import hu.bme.mit.theta.xcfa.model.XcfaEdge;
import hu.bme.mit.theta.xcfa.model.XcfaLabel;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;
import hu.bme.mit.theta.xcfa.model.XcfaProcedureBuilder;
import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.BiFunction;

final class SvLibStatementVisitor extends SvLibBaseVisitor<Set<XcfaLocation>> {

    private final XcfaProcedureBuilder builder;
    private final Map<String, VarDecl<?>> declarations;
    private final SvLibExprVisitor exprVisitor;
    private final String procedureName;
    private final BiFunction<String, String, XcfaLocation> nextLoc;
    private Set<XcfaLocation> currentEntries = Set.of();

    SvLibStatementVisitor(
            XcfaProcedureBuilder builder,
            String procedureName,
            Map<String, VarDecl<?>> declarations,
            SvLibExprVisitor exprVisitor,
            BiFunction<String, String, XcfaLocation> nextLoc) {
        this.builder = builder;
        this.procedureName = procedureName;
        this.declarations = declarations;
        this.exprVisitor = exprVisitor;
        this.nextLoc = nextLoc;
    }

}
