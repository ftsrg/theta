package hu.bme.mit.theta.core.type.fptype;

public enum FpRoundingMode {
	RNE, /* Round nearest ties to even */
	RNA, /* Round nearest ties to away */
	RTP, /* Round toward positive */
	RTN, /* Round toward negative */
	RTZ; /* Round toward zero */

	public static FpRoundingMode getDefaultRoundingMode() {
		return RNA;
	}
}
