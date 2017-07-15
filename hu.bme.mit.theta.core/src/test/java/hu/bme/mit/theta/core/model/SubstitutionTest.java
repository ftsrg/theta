package hu.bme.mit.theta.core.model;

import static hu.bme.mit.theta.core.decl.Decls.Const;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Add;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;

import java.util.Optional;

import org.junit.Assert;
import org.junit.Test;

import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.type.inttype.IntType;

public class SubstitutionTest {
	private final ConstDecl<IntType> ca = Const("a", Int());
	private final ConstDecl<IntType> cb = Const("b", Int());
	private final ConstDecl<IntType> cc = Const("c", Int());

	@Test
	public void testBasic() {
		final Substitution sb = BasicSubstitution.builder().put(ca, Add(Int(1), Int(2))).put(cb, Int(3)).build();
		Assert.assertEquals(2, sb.getDecls().size());
		Assert.assertEquals(Add(Int(1), Int(2)), sb.eval(ca).get());
		Assert.assertEquals(Int(3), sb.eval(cb).get());
		Assert.assertEquals(Optional.empty(), sb.eval(cc));
	}

	@Test
	public void testNested() {
		final Substitution sb1 = BasicSubstitution.builder().put(ca, Int(1)).put(cb, Int(2)).build();
		final Substitution sb2 = BasicSubstitution.builder().put(ca, Int(3)).put(cc, Int(4)).build();
		final NestedSubstitution sb = NestedSubstitution.create(sb1, sb2);
		Assert.assertEquals(3, sb.getDecls().size());
		Assert.assertEquals(Int(3), sb.eval(ca).get());
		Assert.assertEquals(Int(2), sb.eval(cb).get());
		Assert.assertEquals(Int(4), sb.eval(cc).get());
	}

}
