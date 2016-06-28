package hu.bme.mit.inf.ttmc.code;


import org.eclipse.cdt.core.dom.ast.IASTTranslationUnit;
import org.eclipse.cdt.core.dom.ast.gnu.c.GCCLanguage;
import org.eclipse.cdt.core.parser.FileContent;
import org.eclipse.cdt.core.parser.IParserLogService;
import org.eclipse.cdt.core.parser.IncludeFileContentProvider;
import org.eclipse.cdt.core.parser.ScannerInfo;
import org.eclipse.cdt.internal.core.index.CIndex;
import org.eclipse.cdt.internal.core.parser.ParserLogService;
import org.eclipse.core.runtime.CoreException;

import hu.bme.mit.inf.ttmc.code.ast.FunctionDefinitionAst;
import hu.bme.mit.inf.ttmc.code.ast.StatementAst;
import hu.bme.mit.inf.ttmc.code.ast.TranslationUnitAst;
import hu.bme.mit.inf.ttmc.code.simplifier.AstSimplifier;
import hu.bme.mit.inf.ttmc.code.visitor.TransformProgramVisitor;
import hu.bme.mit.inf.ttmc.constraint.ConstraintManagerImpl;
import hu.bme.mit.inf.ttmc.formalism.cfa.CFA;
import hu.bme.mit.inf.ttmc.formalism.cfa.CFACreator;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.Stmt;
import hu.bme.mit.inf.ttmc.formalism.program.ProgramManager;
import hu.bme.mit.inf.ttmc.formalism.program.impl.ProgramManagerImpl;

public class Compiler {

	private ProgramManager pm = new ProgramManagerImpl(new ConstraintManagerImpl());
	
	public CFA createLBE(String filename)
	{
		Stmt content = this.createStmt(filename);
		
		return CFACreator.createLBE(this.pm, content);
	}
	
	public CFA createSBE(String filename)
	{
		Stmt content = this.createStmt(filename);
		
		return CFACreator.createSBE(this.pm, content);
	}
	
	public Stmt createStmt(String filename)
	{
		// Parse with CDT
		IASTTranslationUnit cdtAst;
		try {
			cdtAst = this.parseFile(filename);
			
			// Transform the CDT representation into our custom AST
			TranslationUnitAst root = CdtAstTransformer.transform(cdtAst);
			
			// Simplify the AST for easier transformation 
			TranslationUnitAst newRoot = AstSimplifier.simplify(root);
						
			TransformProgramVisitor transformer = new TransformProgramVisitor(this.pm);
			
			StatementAst funcBody = ((FunctionDefinitionAst) newRoot.getDeclarations().get(0)).getBody();
			Stmt content = funcBody.accept(transformer);
			
			return content;
		} catch (CoreException e) {
			throw new TransformException("Error occured during transform.", e);
		}
	}
	
	private IASTTranslationUnit parseFile(String file) throws CoreException {
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
