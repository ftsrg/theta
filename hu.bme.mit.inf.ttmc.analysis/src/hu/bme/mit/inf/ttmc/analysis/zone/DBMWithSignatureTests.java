package hu.bme.mit.inf.ttmc.analysis.zone;

import java.util.Set;

import org.junit.Test;

import com.google.common.collect.ImmutableSet;

import hu.bme.mit.inf.ttmc.formalism.common.decl.ClockDecl;

public class DBMWithSignatureTests {

	@Test
	public void test() {
		final Set<ClockDecl> clockDecls = ImmutableSet.of();

		final DBMWithSignature dbm1 = DBMWithSignature.top(clockDecls);
		final DBMWithSignature dbm2 = DBMWithSignature.top(clockDecls);
		
		System.out.println(dbm1.getRelation(dbm2));


	}

}
