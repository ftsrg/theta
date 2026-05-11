/*
 *  Copyright 2025 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.frontend.transformation.grammar.preprocess;

import static com.google.common.base.Preconditions.checkState;

import hu.bme.mit.theta.c.frontend.dsl.gen.CParser;
import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.frontend.transformation.grammar.IncludeHandlingCBaseVisitor;
import hu.bme.mit.theta.frontend.transformation.grammar.type.DeclarationVisitor;
import hu.bme.mit.theta.frontend.transformation.model.declaration.CDeclaration;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;

public class GlobalDeclUsageVisitor extends IncludeHandlingCBaseVisitor<List<CDeclaration>> {
    private final DeclarationVisitor declarationVisitor;

    public GlobalDeclUsageVisitor(DeclarationVisitor declarationVisitor) {
        this.declarationVisitor = declarationVisitor;
    }

    public void clear() {
        globalUsages.clear();
        usedContexts.clear();
        current = null;
    }

    private final Map<String, Set<String>> globalUsages = new LinkedHashMap<>();
    private final List<Tuple2<String, CParser.ExternalDeclarationContext>> usedContexts =
            new ArrayList<>();
    private String current;

    @Override
    public List<CDeclaration> visitGlobalDeclaration(CParser.GlobalDeclarationContext ctx) {
        List<CDeclaration> declarations =
                declarationVisitor.getDeclarations(
                        ctx.declaration().declarationSpecifiers(),
                        ctx.declaration().initDeclaratorList(),
                        false);
        for (CDeclaration declaration : declarations) {
            if (!declaration.getType().isTypedef()) {
                globalUsages.remove(declaration.getName());
                globalUsages.put(declaration.getName(), new LinkedHashSet<>());
                if (usedContexts.stream()
                        .anyMatch(c -> Objects.equals(c.get1(), declaration.getName()))) {
                    usedContexts.replaceAll(
                            c ->
                                    Objects.equals(c.get1(), declaration.getName())
                                            ? Tuple2.of(declaration.getName(), ctx)
                                            : c); // keep the order, but overwrite the context
                } else {
                    usedContexts.add(Tuple2.of(declaration.getName(), ctx));
                }
                current = declaration.getName();
                super.visitGlobalDeclaration(ctx);
                current = null;
            }
        }
        return null;
    }

    @Override
    public List<CDeclaration> visitExternalFunctionDefinition(
            CParser.ExternalFunctionDefinitionContext ctx) {
        CDeclaration funcDecl = ctx.functionDefinition().declarator().accept(declarationVisitor);
        globalUsages.put(funcDecl.getName(), new LinkedHashSet<>());
        usedContexts.add(Tuple2.of(funcDecl.getName(), ctx));
        current = funcDecl.getName();
        super.visitExternalFunctionDefinition(ctx);
        current = null;
        return null;
    }

    @Override
    public List<CDeclaration> visitPrimaryExpressionId(CParser.PrimaryExpressionIdContext ctx) {
        globalUsages.get(current).add(ctx.getText());
        return null;
    }

    @Override
    public List<CDeclaration> visitTranslationUnit(CParser.TranslationUnitContext ctx) {
        for (CParser.ExternalDeclarationContext externalDeclarationContext :
                ctx.externalDeclaration()) {
            try {
                externalDeclarationContext.accept(this);
            } catch (Throwable e) {
                // we don't do anything, we'll throw an error later if something's missing
            }
        }
        return null;
    }

    public List<CParser.ExternalDeclarationContext> getGlobalUsages(
            CParser.CompilationUnitContext ctx) {
        globalUsages.clear();
        usedContexts.clear();
        ctx.translationUnit().accept(this);
        checkState(globalUsages.containsKey("main"), "Main function not found!");
        Set<String> ret = new LinkedHashSet<>();
        Set<String> remaining = new LinkedHashSet<>();
        remaining.add("main");
        while (!remaining.isEmpty()) {
            Optional<String> remOpt = remaining.stream().findAny();
            String rem = remOpt.get();
            ret.add(rem);
            Set<String> toAdd =
                    globalUsages.get(rem).stream()
                            .filter(globalUsages::containsKey)
                            .collect(Collectors.toSet());
            remaining.addAll(toAdd);
            remaining.removeAll(ret);
        }
        return usedContexts.stream()
                .filter(objects -> ret.contains(objects.get1()))
                .map(Tuple2::get2)
                .distinct()
                .collect(Collectors.toList());
    }
}
