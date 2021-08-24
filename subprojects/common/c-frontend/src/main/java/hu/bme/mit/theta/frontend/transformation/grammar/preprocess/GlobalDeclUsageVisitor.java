package hu.bme.mit.theta.frontend.transformation.grammar.preprocess;

import hu.bme.mit.theta.c.frontend.dsl.gen.CBaseVisitor;
import hu.bme.mit.theta.c.frontend.dsl.gen.CParser;
import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.frontend.transformation.grammar.type.DeclarationVisitor;
import hu.bme.mit.theta.frontend.transformation.model.declaration.CDeclaration;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;

import static com.google.common.base.Preconditions.checkState;

public class GlobalDeclUsageVisitor extends CBaseVisitor<List<CDeclaration>> {
	public static final GlobalDeclUsageVisitor instance = new GlobalDeclUsageVisitor();

	private final Map<String, Set<String>> globalUsages = new LinkedHashMap<>();
	private final List<Tuple2<String, CParser.ExternalDeclarationContext>> usedContexts = new ArrayList<>();
	private String current;

	@Override
	public List<CDeclaration> visitGlobalDeclaration(CParser.GlobalDeclarationContext ctx) {
		List<CDeclaration> declarations = DeclarationVisitor.instance.getDeclarations(ctx.declaration().declarationSpecifiers(), ctx.declaration().initDeclaratorList());
		for (CDeclaration declaration : declarations) {
			if(!declaration.getType().isTypedef()) {
				globalUsages.put(declaration.getName(), new LinkedHashSet<>());
				usedContexts.add(Tuple2.of(declaration.getName(), ctx));
				current = declaration.getName();
				super.visitGlobalDeclaration(ctx);
				current = null;
			}
		}
		return null;
	}

	@Override
	public List<CDeclaration> visitExternalFunctionDefinition(CParser.ExternalFunctionDefinitionContext ctx) {
		CDeclaration funcDecl = ctx.functionDefinition().declarator().accept(DeclarationVisitor.instance);
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

	public List<CParser.ExternalDeclarationContext> getGlobalUsages(CParser.CompilationUnitContext ctx) {
		globalUsages.clear();
		usedContexts.clear();
		for (CParser.ExternalDeclarationContext externalDeclarationContext : ctx.translationUnit().externalDeclaration()) {
			externalDeclarationContext.accept(this);
		}
		checkState(globalUsages.containsKey("main"), "Main function not found!");
		Set<String> ret = new LinkedHashSet<>();
		Set<String> remaining = new LinkedHashSet<>();
		remaining.add("main");
		while(!remaining.isEmpty()) {
			Optional<String> remOpt = remaining.stream().findAny();
			String rem = remOpt.get();
			ret.add(rem);
			Set<String> toAdd = globalUsages.get(rem).stream().filter(globalUsages::containsKey).collect(Collectors.toSet());
			remaining.addAll(toAdd);
			remaining.removeAll(ret);
		}
		return usedContexts.stream().filter(objects -> ret.contains(objects.get1())).map(Tuple2::get2).distinct().collect(Collectors.toList());
	}
}
