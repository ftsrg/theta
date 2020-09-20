package hu.bme.mit.theta.mcm;

import hu.bme.mit.theta.core.type.inttype.IntLitExpr;
import hu.bme.mit.theta.core.type.inttype.IntType;
import hu.bme.mit.theta.mcm.dsl.McmDslManager;
import hu.bme.mit.theta.mcm.graph.EdgeDB;
import hu.bme.mit.theta.mcm.graph.classification.Thread;
import hu.bme.mit.theta.mcm.graph.classification.Variable;
import hu.bme.mit.theta.mcm.graph.classification.nodes.Node;
import hu.bme.mit.theta.mcm.graph.classification.nodes.Read;
import hu.bme.mit.theta.mcm.graph.classification.nodes.Write;

import java.io.*;
import java.math.BigInteger;
import java.util.List;
import java.util.Map;
import java.util.function.UnaryOperator;

import static hu.bme.mit.theta.core.decl.Decls.Var;

public class VisualTestEdgeDB {

    public static void main(String[] args) {
        EdgeDB edgeDB = EdgeDB.empty();
        Thread threadA = new Thread();
        Thread threadB = new Thread();
        Variable varX = new Variable(Var("x", IntType.getInstance()));
        Variable varY = new Variable(Var("y", IntType.getInstance()));
        Node initialWrite = new Write(Thread.getInitialThread(), varX, IntLitExpr.of(new BigInteger("0")));
        Node threadAWrite = new Write(threadA, varX, IntLitExpr.of(new BigInteger("1")));
        Node threadARead = new Read(threadA, varY);
        Node threadBWrite = new Write(threadB, varY, IntLitExpr.of(new BigInteger("2")));
        Node threadBRead = new Read(threadB, varX);
        edgeDB.addEdge(initialWrite, threadAWrite, "po", false, false);
        edgeDB.addEdge(initialWrite, threadBRead, "po", false, false);
        edgeDB.addEdge(threadAWrite, threadARead, "po", false, false);
        edgeDB.addEdge(threadBRead, threadBWrite, "po", false, false);
        edgeDB.addEdge(initialWrite, threadBRead, "rf", false, false);
        edgeDB.addEdge(threadAWrite, threadARead, "rf", false, false);

        try (InputStream is = new FileInputStream(new File("subprojects/mcm/src/test/resources/test.mcm"))) {
            Map<String, UnaryOperator<List<EdgeDB>>> definitions = McmDslManager.createMCM(is).getDefinitions();
            definitions.forEach((s, rule) -> {
                int i = 0;
                for (EdgeDB edgeDB1 : rule.apply(List.of(edgeDB))) {
                    File file = new File("subprojects/mcm/src/test/resources/out/" + s + "_" + i++ + ".graph");
                    file.getParentFile().mkdirs();
                    try (OutputStream os = new FileOutputStream(file)) {
                        edgeDB1.printGraph(os);
                    } catch (IOException e) {
                        e.printStackTrace();
                    }
                }
            });
        } catch (IOException e) {
            e.printStackTrace();
        }

    }
}
