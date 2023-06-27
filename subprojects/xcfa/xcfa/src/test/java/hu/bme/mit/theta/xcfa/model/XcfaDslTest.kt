package hu.bme.mit.theta.xcfa.model

import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.type.inttype.IntExprs.*
import hu.bme.mit.theta.core.type.inttype.IntType
import hu.bme.mit.theta.xcfa.model.ParamDirection.*
import org.junit.Test

class XcfaDslTest {

    private fun getXcfa() = xcfa("example") {
        lateinit var x: VarDecl<*>
        lateinit var y: VarDecl<*>
        global {
            x = "x" type Int() init "1"
        }
        threadlocal {
            y = "y" type Int() init "2"
        }
        val proc1 = procedure("proc1") {
            "a" type Int() direction IN
            "b" type Int() direction OUT
            val c = "c" type Int() direction INOUT
            val d = "d" type Int()

            (init to final) {
                d assign "a + c"

                havoc("b")
                havoc(c)

                "x" assign d.ref
                "y" assign d.ref
            }
        }
        val main = procedure("main") {
            val ret = "ret" type Int()
            val param = "param" type Int()

            val thr1 = "thr1" type Int()
            val thr2 = "thr2" type Int()
            (init to "L0") {
                param assign "0"
                proc1("1", ret.ref, param.ref)
                thr1.start(proc1, "1", ret.ref, param.ref)
                "thr2".start(proc1, "2", ret.ref, param.ref)
            }
            ("L0" to "L1") {
                thr1.join()
                thr2.join()
            }
            ("L1" to final) {
                assume(Eq(x.ref as RefExpr<IntType>, y.ref as RefExpr<IntType>))
            }
            ("L1" to err) {
                assume("(/= x y)")
            }
        }

        main.start()
    }

    @Test
    fun defineXcfa() {
        getXcfa()
    }

}