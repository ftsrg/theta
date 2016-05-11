package hu.bme.mit.inf.ttmc.analysis.zone;

import static hu.bme.mit.inf.ttmc.analysis.zone.DiffBounds.Leq;
import static hu.bme.mit.inf.ttmc.analysis.zone.DiffBounds.Lt;

import org.junit.Test;

public class DBMTests {

	@Test
	public void test() {
		final DBM dbm = DBM.top(2);

		System.out.println(dbm);
		System.out.println();

		dbm.up();

		System.out.println(dbm);
		System.out.println();

		dbm.and(1, 0, Lt(20));
		dbm.and(2, 0, Leq(20));
		dbm.and(2, 1, Leq(10));
		dbm.and(1, 2, Leq(-10));

		System.out.println(dbm);
		System.out.println();

		dbm.and(1, 0, Lt(-10));

		System.out.println(dbm);

	}
}
