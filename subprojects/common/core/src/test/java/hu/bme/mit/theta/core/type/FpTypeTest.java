package hu.bme.mit.theta.core.type;

import com.google.common.collect.Lists;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.model.ImmutableValuation;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.fptype.FpAddExpr;
import hu.bme.mit.theta.core.type.fptype.FpLitExpr;
import hu.bme.mit.theta.core.type.fptype.FpRoundingMode;
import hu.bme.mit.theta.core.type.fptype.FpType;
import hu.bme.mit.theta.core.utils.FpUtils;
import org.junit.Test;

import java.math.BigDecimal;
import java.util.Collection;
import java.util.Map;
import java.util.Optional;

import static org.junit.Assert.assertEquals;

public class FpTypeTest {
    @Test
    public void testAdd() {
        final FpType type = FpType.of(5, 11);
        final FpLitExpr a = FpUtils.bigDecimalToFpLitExpr(new BigDecimal("2.1"), type);
        final FpLitExpr b = FpUtils.bigDecimalToFpLitExpr(new BigDecimal("3.4"), type);

        final FpAddExpr expr = FpAddExpr.of(FpRoundingMode.RNA, Lists.newArrayList(a, b));

        final BigDecimal res = FpUtils.fpLitExprToBigDecimal(FpRoundingMode.RNA, expr.eval(ImmutableValuation.empty()));
        assertEquals(new BigDecimal("5.5"), res);
    }
}
