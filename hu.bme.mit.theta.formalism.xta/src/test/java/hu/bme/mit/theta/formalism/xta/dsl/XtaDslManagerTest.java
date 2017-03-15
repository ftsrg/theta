package hu.bme.mit.theta.formalism.xta.dsl;

import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;

import org.junit.Test;

public final class XtaDslManagerTest {

	@Test
	public void test() throws FileNotFoundException, IOException {
		final InputStream inputStream = getClass().getResourceAsStream("/cidassignment.xta");
		XtaDslManager.createXta(inputStream);
	}

}
