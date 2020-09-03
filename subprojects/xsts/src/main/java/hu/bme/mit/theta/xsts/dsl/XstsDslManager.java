package hu.bme.mit.theta.xsts.dsl;

import hu.bme.mit.theta.xsts.XSTS;
import hu.bme.mit.theta.xsts.dsl.gen.XstsDslLexer;
import hu.bme.mit.theta.xsts.dsl.gen.XstsDslParser;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;

import java.io.ByteArrayInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.nio.charset.StandardCharsets;

public final class XstsDslManager {

	private XstsDslManager() {
	}

	public static XSTS createXsts(final String inputString) throws IOException {
		final InputStream stream = new ByteArrayInputStream(inputString.getBytes(StandardCharsets.UTF_8.name()));
		return createXsts(stream);
	}

	public static XSTS createXsts(final InputStream inputStream) throws IOException {
		final XstsDslLexer lexer = new XstsDslLexer(CharStreams.fromStream(inputStream));
		final CommonTokenStream tokenStream = new CommonTokenStream(lexer);
		final XstsDslParser parser = new XstsDslParser(tokenStream);
		final XstsDslParser.XstsContext model = parser.xsts();
		final XSTSVisitor visitor = new XSTSVisitor();
		visitor.visitXsts(model);

		return visitor.getXsts();
	}
}
