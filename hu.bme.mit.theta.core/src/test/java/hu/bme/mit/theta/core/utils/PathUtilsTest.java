package hu.bme.mit.theta.core.utils;

import static hu.bme.mit.theta.core.expr.impl.Exprs.Add;
import static hu.bme.mit.theta.core.expr.impl.Exprs.Eq;
import static hu.bme.mit.theta.core.expr.impl.Exprs.Int;
import static hu.bme.mit.theta.core.expr.impl.Exprs.Prime;

import org.junit.Assert;
import org.junit.Test;

import hu.bme.mit.theta.core.decl.IndexedConstDecl;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.decl.impl.Decls;
import hu.bme.mit.theta.core.type.IntType;
import hu.bme.mit.theta.core.type.impl.Types;
import hu.bme.mit.theta.core.utils.impl.PathUtils;

public class PathUtilsTest {

	final VarDecl<IntType> vx = Decls.Var("x", Types.Int());
	final VarDecl<IntType> vy = Decls.Var("y", Types.Int());
	final IndexedConstDecl<IntType> x1 = vx.getConstDecl(1);
	final IndexedConstDecl<IntType> x2 = vx.getConstDecl(2);
	final IndexedConstDecl<IntType> y0 = vy.getConstDecl(0);
	final IndexedConstDecl<IntType> y1 = vy.getConstDecl(1);

	@Test
	public void testUnfold() {
		Assert.assertEquals(Eq(x1.getRef(), Add(y0.getRef(), Int(1))),
				PathUtils.unfold(Eq(Prime(vx.getRef()), Add(vy.getRef(), Int(1))), 0));

		Assert.assertEquals(Eq(x2.getRef(), Add(y1.getRef(), Int(1))),
				PathUtils.unfold(Eq(Prime(vx.getRef()), Add(vy.getRef(), Int(1))), 1));
	}

	@Test
	public void testFold() {
		Assert.assertEquals(Eq(Prime(vx.getRef()), Add(vy.getRef(), Int(1))),
				PathUtils.foldin(Eq(x1.getRef(), Add(y0.getRef(), Int(1))), 0));

		Assert.assertEquals(Eq(Prime(vx.getRef(), 2), Add(Prime(vy.getRef()), Int(1))),
				PathUtils.foldin(Eq(x2.getRef(), Add(y1.getRef(), Int(1))), 0));

		Assert.assertEquals(Eq(Prime(vx.getRef()), Add(vy.getRef(), Int(1))),
				PathUtils.foldin(Eq(x2.getRef(), Add(y1.getRef(), Int(1))), 1));
	}

}
