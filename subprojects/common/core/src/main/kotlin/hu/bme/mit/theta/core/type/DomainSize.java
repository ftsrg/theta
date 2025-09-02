/*
 *  Copyright 2025 Budapest University of Technology and Economics
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */
package hu.bme.mit.theta.core.type;

import static com.google.common.base.Preconditions.checkArgument;

import com.google.common.base.Objects;
import java.math.BigInteger;
import java.util.function.BinaryOperator;

public class DomainSize {

    public static final DomainSize INFINITY = new DomainSize(BigInteger.valueOf(-1));
    public static final DomainSize ZERO = of(0);
    public static final DomainSize ONE = of(1);
    public static final DomainSize TWO = of(2);
    private final BigInteger finiteSize;

    private DomainSize(BigInteger value) {
        finiteSize = value;
    }

    public static DomainSize of(BigInteger val) {
        checkArgument(val.signum() != -1, "DomainSize can't be negative");
        return new DomainSize(val);
    }

    public static DomainSize of(long val) {
        return of(BigInteger.valueOf(val));
    }

    private static DomainSize infiniteForAnyInfiniteApplyElse(
            DomainSize left, DomainSize right, BinaryOperator<BigInteger> operator) {
        if (left.isInfinite() || right.isInfinite()) return INFINITY;
        return of(operator.apply(left.finiteSize, right.finiteSize));
    }

    public static DomainSize add(DomainSize left, DomainSize right) {
        return infiniteForAnyInfiniteApplyElse(left, right, BigInteger::add);
    }

    public static DomainSize multiply(DomainSize left, DomainSize right) {
        return infiniteForAnyInfiniteApplyElse(left, right, BigInteger::multiply);
    }

    /**
     * Raises a domain size to the power of the other. Returns {@link DomainSize#INFINITY} if either
     * parameter is infinite or exponent is too large ( = can't fit into an integer)
     */
    public static DomainSize pow(DomainSize base, DomainSize exponent) {
        if (base.isInfinite() || exponent.isInfinite()) return INFINITY;
        int iExp;
        try {
            iExp = exponent.finiteSize.intValueExact();
        } catch (ArithmeticException exception) {
            return INFINITY;
        }
        return of(base.finiteSize.pow(iExp));
    }

    public boolean isInfinite() {
        return equals(INFINITY);
    }

    public boolean isBiggerThan(long limit) {
        return this.equals(INFINITY) || finiteSize.compareTo(BigInteger.valueOf(limit)) > 0;
    }

    public BigInteger getFiniteSize() {
        return finiteSize;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        DomainSize that = (DomainSize) o;
        return Objects.equal(finiteSize, that.finiteSize);
    }

    @Override
    public int hashCode() {
        return Objects.hashCode(finiteSize);
    }
}
