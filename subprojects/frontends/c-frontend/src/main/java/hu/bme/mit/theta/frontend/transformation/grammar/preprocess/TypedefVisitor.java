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

import hu.bme.mit.theta.c.frontend.dsl.gen.CParser;
import hu.bme.mit.theta.frontend.transformation.grammar.IncludeHandlingCBaseVisitor;
import hu.bme.mit.theta.frontend.transformation.grammar.type.DeclarationVisitor;
import hu.bme.mit.theta.frontend.transformation.model.declaration.CDeclaration;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType;
import hu.bme.mit.theta.frontend.transformation.model.types.simple.CSimpleType;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Optional;
import java.util.Set;
import org.antlr.v4.runtime.tree.ParseTree;

public class TypedefVisitor extends IncludeHandlingCBaseVisitor<Set<CDeclaration>> {
    private final DeclarationVisitor declarationVisitor;

    public TypedefVisitor(DeclarationVisitor declarationVisitor) {
        this.declarationVisitor = declarationVisitor;
    }

    public void clear() {
        declarations.clear();
    }

    private final Set<CDeclaration> declarations = new LinkedHashSet<>();

    public Optional<CComplexType> getType(String id) {
        return declarations.stream()
                .filter(cDeclaration -> cDeclaration.getName().equals(id))
                .map(CDeclaration::getActualType)
                .findFirst();
    }

    public Optional<CSimpleType> getSimpleType(String id) {
        return declarations.stream()
                .filter(cDeclaration -> cDeclaration.getName().equals(id))
                .map(CDeclaration::getType)
                .findFirst();
    }

    @Override
    public Set<CDeclaration> visitDeclaration(CParser.DeclarationContext ctx) {
        Set<CDeclaration> ret = new LinkedHashSet<>();
        if (ctx.declarationSpecifiers().declarationSpecifier(0).getText().equals("typedef")) {
            List<CDeclaration> declarations =
                    declarationVisitor.getDeclarations(
                            ctx.declarationSpecifiers(), ctx.initDeclaratorList());
            this.declarations.addAll(declarations);
            ret.addAll(declarations);
            return ret;
        } else return null;
    }

    @Override
    public Set<CDeclaration> visitBlockItemList(CParser.BlockItemListContext ctx) {
        Set<CDeclaration> ret = new LinkedHashSet<>();
        for (ParseTree child : ctx.children) {
            Set<CDeclaration> list = child.accept(this);
            if (list != null) {
                this.declarations.addAll(list);
                ret.addAll(list);
            }
        }
        return ret;
    }

    @Override
    public Set<CDeclaration> visitCompoundStatement(CParser.CompoundStatementContext ctx) {
        Set<CDeclaration> ret = new LinkedHashSet<>();
        for (ParseTree child : ctx.children) {
            Set<CDeclaration> list = child.accept(this);
            if (list != null) {
                this.declarations.addAll(list);
                ret.addAll(list);
            }
        }
        return ret;
    }

    @Override
    public Set<CDeclaration> visitGlobalDeclaration(CParser.GlobalDeclarationContext ctx) {
        Set<CDeclaration> ret = new LinkedHashSet<>();
        if (ctx.declaration()
                .declarationSpecifiers()
                .declarationSpecifier(0)
                .getText()
                .equals("typedef")) {
            List<CDeclaration> declarations =
                    declarationVisitor.getDeclarations(
                            ctx.declaration().declarationSpecifiers(),
                            ctx.declaration().initDeclaratorList());
            ret.addAll(declarations);
            this.declarations.addAll(declarations);
            return ret;
        }
        return null;
    }

    @Override
    public Set<CDeclaration> visitCompilationUnit(CParser.CompilationUnitContext ctx) {
        declarations.clear();
        CParser.TranslationUnitContext translationUnitContext = ctx.translationUnit();
        if (translationUnitContext != null) {
            for (CParser.ExternalDeclarationContext externalDeclarationContext :
                    translationUnitContext.externalDeclaration()) {
                try {
                    Set<CDeclaration> declList = externalDeclarationContext.accept(this);
                    if (declList != null) {
                        declarations.addAll(declList);
                    }
                } catch (Throwable e) {
                    // we don't do anything, we'll throw an error later if something crucial is
                    // missing
                    e.printStackTrace();
                }
            }
        }
        return declarations;
    }
}
