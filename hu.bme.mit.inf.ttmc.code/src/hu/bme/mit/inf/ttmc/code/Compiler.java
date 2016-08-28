package hu.bme.mit.inf.ttmc.code;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.cdt.core.dom.ast.IASTTranslationUnit;
import org.eclipse.cdt.core.dom.ast.gnu.c.GCCLanguage;
import org.eclipse.cdt.core.parser.FileContent;
import org.eclipse.cdt.core.parser.IParserLogService;
import org.eclipse.cdt.core.parser.IncludeFileContentProvider;
import org.eclipse.cdt.core.parser.ScannerInfo;
import org.eclipse.cdt.internal.core.index.CIndex;
import org.eclipse.cdt.internal.core.parser.ParserLogService;
import org.eclipse.core.runtime.CoreException;

import hu.bme.mit.inf.ttmc.code.ast.DeclarationAst;
import hu.bme.mit.inf.ttmc.code.ast.FunctionDefinitionAst;
import hu.bme.mit.inf.ttmc.code.ast.TranslationUnitAst;
import hu.bme.mit.inf.ttmc.code.simplifier.AstSimplifier;
import hu.bme.mit.inf.ttmc.code.visitor.StmtTransformProgramVisitor;
import hu.bme.mit.inf.ttmc.core.type.Type;
import hu.bme.mit.inf.ttmc.core.type.impl.Types;
import hu.bme.mit.inf.ttmc.formalism.common.decl.ProcDecl;
import hu.bme.mit.inf.ttmc.frontend.ir.Function;
import hu.bme.mit.inf.ttmc.frontend.ir.GlobalContext;

public class Compiler {

	public static GlobalContext compile(String filename) {
		TranslationUnitAst root = createSimplifiedAst(filename);
		GlobalContext context = new GlobalContext();

		root.getDeclarations().forEach(decl -> {
			if (decl instanceof FunctionDefinitionAst) {
				FunctionDefinitionAst funcAst = (FunctionDefinitionAst) decl;
				Function func = new Function(funcAst.getName(), Types.Int());

				IrCodeGenerator codegen = new IrCodeGenerator(func);
				codegen.generate(funcAst);

				context.addFunction(func);
			}
		});

		return context;
	}

	/*
	public static List<CFA> createLBE(String filename)
	{
		List<CFA> cfas = new ArrayList<>();
		List<ProcDecl<? extends Type>> procs = createStmts(filename);

		for (ProcDecl<? extends Type> proc : procs) {
			cfas.add(CFACreator.createLBE(proc.getStmt().get()));
		}

		return cfas;
	}

	public static List<CFA> createSBE(String filename)
	{
		List<CFA> cfas = new ArrayList<>();
		List<ProcDecl<? extends Type>> procs = createStmts(filename);

		for (ProcDecl<? extends Type> proc : procs) {
			cfas.add(CFACreator.createSBE(proc.getStmt().get()));
		}

		return cfas;
	} */

	public static List<ProcDecl<? extends Type>> createStmts(String filename)
	{
		TranslationUnitAst root = createSimplifiedAst(filename);

		StmtTransformProgramVisitor transformer = new StmtTransformProgramVisitor();

		List<ProcDecl<? extends Type>> topDecls = new ArrayList<>();

		for (DeclarationAst decl : root.getDeclarations()) {
			if (decl instanceof FunctionDefinitionAst) {
				ProcDecl<? extends Type> proc = (ProcDecl<? extends Type>) decl.accept(transformer);
				topDecls.add(proc);
			}
		}

		return topDecls;
	}


	public static TranslationUnitAst createSimplifiedAst(String filename)
	{
		TranslationUnitAst root = createAst(filename);

		// Simplify the AST for easier transformation
		TranslationUnitAst newRoot = AstSimplifier.simplify(root);

		return newRoot;
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
			throw new TransformException("Error occured during transform.", e);
		}
	}

	private static IASTTranslationUnit parseFile(String file) throws CoreException {
		GCCLanguage lang = new GCCLanguage();

		FileContent fc = FileContent.createForExternalFileLocation(file);
		ScannerInfo sc = new ScannerInfo();

		IncludeFileContentProvider ifcp = IncludeFileContentProvider.getEmptyFilesProvider();
		CIndex index = new CIndex(null);

		IParserLogService log = new ParserLogService(null);

		IASTTranslationUnit ast = lang.getASTTranslationUnit(fc, sc, ifcp, index, 0, log);

		return ast;
	}

}
