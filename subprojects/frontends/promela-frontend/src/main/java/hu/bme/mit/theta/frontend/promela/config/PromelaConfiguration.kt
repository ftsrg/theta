package hu.bme.mit.theta.frontend.promela.config

import java.math.BigInteger

sealed class PromelaConfiguration (
    // bit widths of types
    val UCHAR_BIT : Int, // unsigned
    val SHRT_BIT : Int, // signed
    val INT_BIT : Int, // signed
)