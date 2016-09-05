package hu.bme.mit.inf.ttmc.code;

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

import hu.bme.mit.inf.ttmc.code.ast.FunctionDefinitionAst;
import hu.bme.mit.inf.ttmc.code.ast.TranslationUnitAst;
import hu.bme.mit.inf.ttmc.core.type.impl.Types;
import hu.bme.mit.inf.ttmc.frontend.ir.Function;
import hu.bme.mit.inf.ttmc.frontend.ir.GlobalContext;

public class Parser {

	public static GlobalContext parse(String filename) {
		TranslationUnitAst root = createAst(filename);
		GlobalContext context = new GlobalContext();

		root.getDeclarations().forEach(decl -> {
			if (decl instanceof FunctionDefinitionAst) {
				FunctionDefinitionAst funcAst = (FunctionDefinitionAst) decl;
				Function func = new Function(funcAst.getName(), Types.Int());

				IrCodeGenerator codegen = new IrCodeGenerator(context, func);
				codegen.generate(funcAst);

				context.addFunction(func);
			}
		});

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
