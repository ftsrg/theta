package hu.bme.mit.theta.core.utils;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.math.MathContext;

public class IEEEBigDecimal {
	public static final IEEEBigDecimal NaN = new IEEEBigDecimal();
	public static final IEEEBigDecimal POSITIVE_INFINITY = new IEEEBigDecimal();
	public static final IEEEBigDecimal NEGATIVE_INFINITY = new IEEEBigDecimal();

	public static final IEEEBigDecimal ZERO = new IEEEBigDecimal("0");
	public static final IEEEBigDecimal ONE = new IEEEBigDecimal("1");
	public static final IEEEBigDecimal TWO = new IEEEBigDecimal("2");
	public static final IEEEBigDecimal TEN = new IEEEBigDecimal("10");

	private final BigDecimal bigDecimal;

	private IEEEBigDecimal() {
		bigDecimal = null;
	}

	public IEEEBigDecimal(final String val) {
		bigDecimal = new BigDecimal(val);
	}

	public IEEEBigDecimal(final BigInteger bigInteger) {
		this.bigDecimal = new BigDecimal(bigInteger);
	}

	public IEEEBigDecimal(final BigDecimal bigDecimal) {
		this.bigDecimal = bigDecimal;
	}

	public IEEEBigDecimal add(final IEEEBigDecimal augend, final MathContext mc) {
		if (this == NaN || augend == NaN) {
			return NaN;
		} else if (this == POSITIVE_INFINITY) {
			if (augend == POSITIVE_INFINITY) {
				return POSITIVE_INFINITY;
			} else if (augend == NEGATIVE_INFINITY) {
				return NaN;
			} else {
				return POSITIVE_INFINITY;
			}
		} else if (this == NEGATIVE_INFINITY) {
			if (augend == POSITIVE_INFINITY) {
				return NaN;
			} else if (augend == NEGATIVE_INFINITY) {
				return NEGATIVE_INFINITY;
			} else {
				return NEGATIVE_INFINITY;
			}
		} else {
			if (augend == POSITIVE_INFINITY) {
				return POSITIVE_INFINITY;
			} else if (augend == NEGATIVE_INFINITY) {
				return NEGATIVE_INFINITY;
			} else {
				assert bigDecimal != null;
				return new IEEEBigDecimal(bigDecimal.add(augend.bigDecimal, mc));
			}
		}
	}

	public IEEEBigDecimal subtract(final IEEEBigDecimal subtrahend, final MathContext mc) {
		if (this == NaN || subtrahend == NaN) {
			return NaN;
		} else if (this == POSITIVE_INFINITY) {
			if (subtrahend == POSITIVE_INFINITY) {
				return NaN;
			} else if (subtrahend == NEGATIVE_INFINITY) {
				return POSITIVE_INFINITY;
			} else {
				return POSITIVE_INFINITY;
			}
		} else if (this == NEGATIVE_INFINITY) {
			if (subtrahend == POSITIVE_INFINITY) {
				return NEGATIVE_INFINITY;
			} else if (subtrahend == NEGATIVE_INFINITY) {
				return NaN;
			} else {
				return NEGATIVE_INFINITY;
			}
		} else {
			if (subtrahend == POSITIVE_INFINITY) {
				return NEGATIVE_INFINITY;
			} else if (subtrahend == NEGATIVE_INFINITY) {
				return POSITIVE_INFINITY;
			} else {
				assert bigDecimal != null;
				return new IEEEBigDecimal(bigDecimal.subtract(subtrahend.bigDecimal, mc));
			}
		}
	}

	public IEEEBigDecimal negate() {
		if (this == NaN) {
			return NaN;
		} else if (this == POSITIVE_INFINITY) {
			return NEGATIVE_INFINITY;
		} else if (this == NEGATIVE_INFINITY) {
			return POSITIVE_INFINITY;
		} else {
			assert bigDecimal != null;
			return new IEEEBigDecimal(bigDecimal.negate());
		}
	}

	public IEEEBigDecimal multiply(final IEEEBigDecimal multiplicand, final MathContext mc) {
		if (this == NaN || multiplicand == NaN) {
			return NaN;
		} else if (this == POSITIVE_INFINITY) {
			if (multiplicand == POSITIVE_INFINITY) {
				return POSITIVE_INFINITY;
			} else if (multiplicand == NEGATIVE_INFINITY) {
				return NEGATIVE_INFINITY;
			} else {
				if (this.isLessThan(ZERO)) {
					return NEGATIVE_INFINITY;
				} else if (this.isGreaterThan(ZERO)) {
					return POSITIVE_INFINITY;
				} else {
					return NaN;
				}
			}
		} else if (this == NEGATIVE_INFINITY) {
			if (multiplicand == POSITIVE_INFINITY) {
				return NEGATIVE_INFINITY;
			} else if (multiplicand == NEGATIVE_INFINITY) {
				return POSITIVE_INFINITY;
			} else {
				if (this.isLessThan(ZERO)) {
					return POSITIVE_INFINITY;
				} else if (this.isGreaterThan(ZERO)) {
					return NEGATIVE_INFINITY;
				} else {
					return NaN;
				}
			}
		} else {
			if (multiplicand == POSITIVE_INFINITY) {
				if (this.isLessThan(ZERO)) {
					return NEGATIVE_INFINITY;
				} else if (this.isGreaterThan(ZERO)) {
					return POSITIVE_INFINITY;
				} else {
					return NaN;
				}
			} else if (multiplicand == NEGATIVE_INFINITY) {
				if (this.isLessThan(ZERO)) {
					return POSITIVE_INFINITY;
				} else if (this.isGreaterThan(ZERO)) {
					return NEGATIVE_INFINITY;
				} else {
					return NaN;
				}
			} else {
				assert bigDecimal != null;
				return new IEEEBigDecimal(bigDecimal.multiply(multiplicand.bigDecimal, mc));
			}
		}
	}

	public IEEEBigDecimal divide(final IEEEBigDecimal divisor, final MathContext mc) {
		if (this == NaN || divisor == NaN) {
			return NaN;
		} else if (this == POSITIVE_INFINITY) {
			if (divisor == POSITIVE_INFINITY) {
				return NaN;
			} else if (divisor == NEGATIVE_INFINITY) {
				return NaN;
			} else {
				if (this.isLessThan(ZERO)) {
					return NEGATIVE_INFINITY;
				} else {
					return POSITIVE_INFINITY;
				}
			}
		} else if (this == NEGATIVE_INFINITY) {
			if (divisor == POSITIVE_INFINITY) {
				return NaN;
			} else if (divisor == NEGATIVE_INFINITY) {
				return NaN;
			} else {
				if (this.isLessThan(ZERO)) {
					return POSITIVE_INFINITY;
				} else {
					return NEGATIVE_INFINITY;
				}
			}
		} else {
			if (divisor == POSITIVE_INFINITY) {
				return ZERO;
			} else if (divisor == NEGATIVE_INFINITY) {
				return ZERO;
			} else {
				assert bigDecimal != null;
				return new IEEEBigDecimal(bigDecimal.divide(divisor.bigDecimal, mc));
			}
		}
	}

	public IEEEBigDecimal pow(final int exponent, final MathContext mc) {
		if (this == NaN) {
			return NaN;
		} else if (this == POSITIVE_INFINITY) {
			if (exponent < 0) {
				return ZERO;
			} else if (exponent == 0) {
				return ONE;
			} else {
				return POSITIVE_INFINITY;
			}
		} else if (this == NEGATIVE_INFINITY) {
			if (exponent < 0) {
				return ZERO;
			} else if (exponent == 0) {
				return ONE;
			} else {
				return exponent % 2 == 0 ? POSITIVE_INFINITY : NEGATIVE_INFINITY;
			}
		} else {
			assert bigDecimal != null;
			return new IEEEBigDecimal(bigDecimal.pow(exponent, mc));
		}
	}

	public boolean isLessThan(final IEEEBigDecimal ieeeBigDecimal) {
		if (this == NaN || ieeeBigDecimal == NaN) {
			return false;
		}
		if (this == POSITIVE_INFINITY) {
			return false;
		} else if (this == NEGATIVE_INFINITY) {
			return ieeeBigDecimal != NEGATIVE_INFINITY;
		} else {
			if (ieeeBigDecimal == POSITIVE_INFINITY) {
				return true;
			} else if (ieeeBigDecimal == NEGATIVE_INFINITY) {
				return false;
			} else {
				assert bigDecimal != null;
				return bigDecimal.compareTo(ieeeBigDecimal.bigDecimal) < 0;
			}
		}
	}

	public boolean isLessThanEqual(final IEEEBigDecimal ieeeBigDecimal) {
		if (this == NaN || ieeeBigDecimal == NaN) {
			return false;
		}
		if (this == POSITIVE_INFINITY) {
			return ieeeBigDecimal == POSITIVE_INFINITY;
		} else if (this == NEGATIVE_INFINITY) {
			return true;
		} else {
			if (ieeeBigDecimal == POSITIVE_INFINITY) {
				return true;
			} else if (ieeeBigDecimal == NEGATIVE_INFINITY) {
				return false;
			} else {
				assert bigDecimal != null;
				return bigDecimal.compareTo(ieeeBigDecimal.bigDecimal) <= 0;
			}
		}
	}

	public boolean isGreaterThan(final IEEEBigDecimal ieeeBigDecimal) {
		if (this == NaN || ieeeBigDecimal == NaN) {
			return false;
		}
		if (this == POSITIVE_INFINITY) {
			return ieeeBigDecimal != POSITIVE_INFINITY;
		} else if (this == NEGATIVE_INFINITY) {
			return false;
		} else {
			if (ieeeBigDecimal == POSITIVE_INFINITY) {
				return false;
			} else if (ieeeBigDecimal == NEGATIVE_INFINITY) {
				return true;
			} else {
				assert bigDecimal != null;
				return bigDecimal.compareTo(ieeeBigDecimal.bigDecimal) > 0;
			}
		}
	}

	public boolean isGreaterThanEqual(final IEEEBigDecimal ieeeBigDecimal) {
		if (this == NaN || ieeeBigDecimal == NaN) {
			return false;
		}
		if (this == POSITIVE_INFINITY) {
			return true;
		} else if (this == NEGATIVE_INFINITY) {
			return ieeeBigDecimal == NEGATIVE_INFINITY;
		} else {
			if (ieeeBigDecimal == POSITIVE_INFINITY) {
				return false;
			} else if (ieeeBigDecimal == NEGATIVE_INFINITY) {
				return true;
			} else {
				assert bigDecimal != null;
				return bigDecimal.compareTo(ieeeBigDecimal.bigDecimal) >= 0;
			}
		}
	}

	public BigInteger unscaledValue() {
		if (this == NaN || this == POSITIVE_INFINITY || this == NEGATIVE_INFINITY) {
			throw new IllegalStateException("NaN or Infinity does not have unscaled value");
		}
		assert bigDecimal != null;
		return bigDecimal.unscaledValue();
	}

	public int scale() {
		if (this == NaN || this == POSITIVE_INFINITY || this == NEGATIVE_INFINITY) {
			throw new IllegalStateException("NaN or Infinity does not have scale");
		}
		assert bigDecimal != null;
		return bigDecimal.scale();
	}

	@Override
	public boolean equals(final Object x) {
		if (this == NaN || x == NaN) return this == x;
		else if (this == POSITIVE_INFINITY || x == POSITIVE_INFINITY) return this == x;
		else if (this == NEGATIVE_INFINITY || x == NEGATIVE_INFINITY) return this == x;
		else {
			assert bigDecimal != null;
			return bigDecimal.equals(x);
		}
	}

	@Override
	public String toString() {
		if (this == NaN) return "NaN";
		else if (this == POSITIVE_INFINITY) return "+Infinity";
		else if (this == NEGATIVE_INFINITY) return "-Infinity";
		else {
			assert bigDecimal != null;
			return bigDecimal.toString();
		}
	}
}
