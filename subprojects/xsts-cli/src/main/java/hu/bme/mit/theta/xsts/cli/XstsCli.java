package hu.bme.mit.theta.xsts.cli;

import hu.bme.mit.theta.core.utils.StmtUtils;
import hu.bme.mit.theta.core.utils.VarIndexing;
import hu.bme.mit.theta.xsts.XSTS;
import hu.bme.mit.theta.xsts.dsl.XSTSVisitor;
import hu.bme.mit.theta.xsts.dsl.gen.XstsDslLexer;
import hu.bme.mit.theta.xsts.dsl.gen.XstsDslParser;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;

public class XstsCli {

    public static void main(String[] args){
        try {
            XstsDslLexer lexer=new XstsDslLexer(CharStreams.fromFileName("src/test/resources/trafficlight.xsts"));
            CommonTokenStream tokenStream=new CommonTokenStream(lexer);
            XstsDslParser parser=new XstsDslParser(tokenStream);
            XstsDslParser.XstsContext model =parser.xsts();
            XSTSVisitor visitor=new XSTSVisitor();
            visitor.visitXsts(model);
            XSTS xsts=visitor.getXsts();

            System.out.println(StmtUtils.toExpr(xsts.getEnvAction(), VarIndexing.all(0)).getIndexing());
        } catch (Exception e){
            e.printStackTrace();
        }

    }

}
