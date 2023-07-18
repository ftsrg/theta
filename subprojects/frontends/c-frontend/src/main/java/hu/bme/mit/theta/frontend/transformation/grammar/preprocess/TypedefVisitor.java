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

package hu.bme.mit.theta.frontend.transformation.grammar.preprocess;

import hu.bme.mit.theta.c.frontend.dsl.gen.CBaseVisitor;
import hu.bme.mit.theta.c.frontend.dsl.gen.CParser;
import hu.bme.mit.theta.frontend.transformation.grammar.type.DeclarationVisitor;
import hu.bme.mit.theta.frontend.transformation.model.declaration.CDeclaration;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType;
import org.antlr.v4.runtime.tree.ParseTree;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

public class TypedefVisitor extends CBaseVisitor<List<CDeclaration>> {
    private final DeclarationVisitor declarationVisitor;

    public TypedefVisitor(DeclarationVisitor declarationVisitor) {
        this.declarationVisitor = declarationVisitor;
    }

    public void clear() {
        declarations.clear();
    }

    private final List<CDeclaration> declarations = new ArrayList<>();

    public Optional<CComplexType> getType(String id) {
        return declarations.stream().filter(cDeclaration -> cDeclaration.getName().equals(id)).map(CDeclaration::getActualType).findFirst();
    }

    @Override
    public List<CDeclaration> visitDeclaration(CParser.DeclarationContext ctx) {
        List<CDeclaration> ret = new ArrayList<>();
        if (ctx.declarationSpecifiers().declarationSpecifier(0).getText().equals("typedef")) {
            List<CDeclaration> declarations = declarationVisitor.getDeclarations(ctx.declarationSpecifiers(), ctx.initDeclaratorList());
            ret.addAll(declarations);
            return ret;
        } else return null;
    }

    @Override
    public List<CDeclaration> visitBlockItemList(CParser.BlockItemListContext ctx) {
        List<CDeclaration> ret = new ArrayList<>();
        for (ParseTree child : ctx.children) {
            List<CDeclaration> list = child.accept(this);
            if (list != null) ret.addAll(list);
        }
        return ret;
    }

    @Override
    public List<CDeclaration> visitCompoundStatement(CParser.CompoundStatementContext ctx) {
        List<CDeclaration> ret = new ArrayList<>();
        for (ParseTree child : ctx.children) {
            List<CDeclaration> list = child.accept(this);
            if (list != null) ret.addAll(list);
        }
        return ret;
    }

    @Override
    public List<CDeclaration> visitGlobalDeclaration(CParser.GlobalDeclarationContext ctx) {
        List<CDeclaration> ret = new ArrayList<>();
        if (ctx.declaration().declarationSpecifiers().declarationSpecifier(0).getText().equals("typedef")) {
            List<CDeclaration> declarations = declarationVisitor.getDeclarations(ctx.declaration().declarationSpecifiers(), ctx.declaration().initDeclaratorList());
            ret.addAll(declarations);
            return ret;
        }
        return null;
    }

    @Override
    public List<CDeclaration> visitCompilationUnit(CParser.CompilationUnitContext ctx) {
        declarations.clear();
        CParser.TranslationUnitContext translationUnitContext = ctx.translationUnit();
        if (translationUnitContext != null) {
            for (CParser.ExternalDeclarationContext externalDeclarationContext : translationUnitContext.externalDeclaration()) {
                List<CDeclaration> declList = externalDeclarationContext.accept(this);
                if (declList != null) {
                    declarations.addAll(declList);
                }
            }
        }
        return declarations;
    }
}
