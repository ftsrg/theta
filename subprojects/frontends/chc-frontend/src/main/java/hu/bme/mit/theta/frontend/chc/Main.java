package hu.bme.mit.theta.frontend.chc;

import hu.bme.mit.theta.xcfa.model.XCFA;
import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.CharStreams;

import java.io.IOException;
import java.util.List;

public class Main {
    static List<String> testFiles = List.of(
            "chc-DEMO.smt2",
            "chc-LIA-Lin_000.smt2",
            "chc-LIA-Lin_001.smt2",
            "chc-LIA-Lin_002.smt2",
            "chc-LIA-NonLin_000.smt2",
            "chc-LIA-NonLin_001.smt2"
    );

    public static void main(String[] args) {
        CharStream charStream;
        try {
            charStream = CharStreams.fromFileName("subprojects/frontends/chc-frontend/src/main/resources/" + testFiles.get(0));
        } catch (IOException e) {
            throw new RuntimeException(e);
        }

        ChcFrontend.chcTransformation = ChcFrontend.ChcTransformation.BACKWARD;
        ChcUtils.setCharStream(charStream);
        ChcFrontend frontend = new ChcFrontend();
        XCFA.Builder builder = frontend.buildXcfa(charStream);
        XCFA xcfa = builder.build();
        System.out.println(xcfa.toDot());
    }
}
