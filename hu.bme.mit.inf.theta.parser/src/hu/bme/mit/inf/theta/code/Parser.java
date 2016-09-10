package hu.bme.mit.inf.theta.code;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import org.eclipse.cdt.core.dom.ast.IASTTranslationUnit;
import org.eclipse.cdt.core.dom.ast.gnu.c.GCCLanguage;
import org.eclipse.cdt.core.index.IIndex;
import org.eclipse.cdt.core.parser.FileContent;
import org.eclipse.cdt.core.parser.IParserLogService;
import org.eclipse.cdt.core.parser.IncludeFileContentProvider;
import org.eclipse.cdt.core.parser.ScannerInfo;
import org.eclipse.cdt.internal.core.index.CIndex;
import org.eclipse.cdt.internal.core.parser.ParserLogService;
import org.eclipse.core.runtime.CoreException;

import hu.bme.mit.inf.theta.code.ast.DeclarationAst;
import hu.bme.mit.inf.theta.code.ast.DeclaratorAst;
import hu.bme.mit.inf.theta.code.ast.FunctionDeclaratorAst;
import hu.bme.mit.inf.theta.code.ast.FunctionDefinitionAst;
import hu.bme.mit.inf.theta.code.ast.ParameterDeclarationAst;
import hu.bme.mit.inf.theta.code.ast.TranslationUnitAst;
import hu.bme.mit.inf.theta.code.ast.VarDeclarationAst;
import hu.bme.mit.inf.theta.code.ast.utils.AstPrinter;
import hu.bme.mit.inf.theta.frontend.ir.Function;
import hu.bme.mit.inf.theta.frontend.ir.GlobalContext;
import hu.bme.mit.inf.theta.core.decl.ParamDecl;
import hu.bme.mit.inf.theta.core.decl.impl.Decls;
import hu.bme.mit.inf.theta.core.expr.impl.Exprs;
import hu.bme.mit.inf.theta.core.type.Type;
import hu.bme.mit.inf.theta.core.type.impl.Types;
import hu.bme.mit.inf.theta.formalism.common.decl.ProcDecl;
import hu.bme.mit.inf.theta.formalism.common.decl.impl.Decls2;
import hu.bme.mit.inf.theta.formalism.common.expr.impl.Exprs2;

public class Parser {

	public static GlobalContext parse(String filename) {
		TranslationUnitAst root = createAst(filename);
		GlobalContext context = new GlobalContext();

		for (DeclarationAst decl : root.getDeclarations()) {
			if (decl instanceof FunctionDefinitionAst) {
				FunctionDefinitionAst funcAst = (FunctionDefinitionAst) decl;
				String name = funcAst.getName();

				List<ParamDecl<?>> params = new ArrayList<>();
				for (ParameterDeclarationAst param : funcAst.getDeclarator().getParameters()) {
					params.add(Decls.Param(param.getDeclarator().getName(), Types.Int()));
				}

				ProcDecl<? extends Type> proc = Decls2.Proc(name, params, Types.Int());

				Function func = new Function(name, proc);
				context.addFunction(func, proc);
				context.getSymbolTable().put(name, proc);

				// create a new function scope and add all function parameters to it
				IrCodeGenerator codegen = new IrCodeGenerator(context, func);
				codegen.generate(funcAst);

			} else if (decl instanceof VarDeclarationAst) {
				// It may be a global variable or a function declaration
				for (DeclaratorAst declarator : ((VarDeclarationAst) decl).getDeclarators()) {
					if (declarator instanceof FunctionDeclaratorAst) {
						FunctionDeclaratorAst funcDeclarator = (FunctionDeclaratorAst) declarator;

						ProcDecl<? extends Type> proc = Decls2.Proc(funcDeclarator.getName(), Collections.emptyList(), Types.Int());
						context.addFunctionDeclaration(funcDeclarator.getName(), proc);
					} else {
						// TODO: Treat it as a global variable
						throw new UnsupportedOperationException("Global variables are not supported");
					}
				}
			}
		}

		return context;
	}

	public static TranslationUnitAst createAst(String filename)
	{
		try {
			// Parse with CDT
			IASTTranslationUnit cdtAst = parseFile(filename);
			// Transform the CDT representation into our custom AST
			TranslationUnitAst root = CdtAstTransformer.transform(cdtAst);

			return root;
		} catch (CoreException e) {
			throw new ParserException("Error occured during transform.", e);
		}
	}

	private static IASTTranslationUnit parseFile(String file) throws CoreException {
		GCCLanguage lang = new GCCLanguage();

		FileContent fc = FileContent.createForExternalFileLocation(file);
		ScannerInfo sc = new ScannerInfo();

		IncludeFileContentProvider ifcp = IncludeFileContentProvider.getEmptyFilesProvider();
		IIndex index = new CIndex(null);
		IParserLogService log = new ParserLogService(null);

		IASTTranslationUnit ast = lang.getASTTranslationUnit(fc, sc, ifcp, index, 0, log);

		return ast;
	}

}
