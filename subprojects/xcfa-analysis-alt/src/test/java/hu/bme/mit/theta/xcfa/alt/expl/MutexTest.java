package hu.bme.mit.theta.xcfa.alt.expl;

import hu.bme.mit.theta.xcfa.XCFA;
import hu.bme.mit.theta.xcfa.type.SyntheticLitExpr;
import org.junit.Assert;
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Test;

import java.util.Map;

public class MutexTest {

    // processes does not have a state, so it can be initialized once for all tests.
    static XCFA.Process process1;
    static XCFA.Process process2;

    SyntheticLitExpr lock1;
    SyntheticLitExpr lock2;

    // TODO there was a helper function.
    private static XCFA.Process createProcess() {
        // TODO create a Process.createEmpty() or
        //     use interface instead of XCFA.Process
        var builder = XCFA.Process.builder();
        var procBuilder = XCFA.Process.Procedure.builder();
        XCFA.Process.Procedure.Location l0 = new XCFA.Process.Procedure.Location("", Map.of());
        XCFA.Process.Procedure.Location l1 = new XCFA.Process.Procedure.Location("", Map.of());
        procBuilder.addLoc(l0);
        procBuilder.addLoc(l1);
        procBuilder.setInitLoc(l0);
        procBuilder.setFinalLoc(l1);
        var proc = procBuilder.build();
        builder.addProcedure(proc);
        builder.setMainProcedure(proc);
        return builder.build();
    }

    @BeforeClass
    public static void initProcesses() {
        process1 = createProcess();
        process2 = createProcess();
    }

    @Before
    public void init() {
        lock1 = SyntheticLitExpr.unlocked();
        lock2 = SyntheticLitExpr.unlocked();
    }

    @Test
    public void lockTest() {
        lock1 = lock1.lock(process1).get();
        Assert.assertTrue(lock1.isValid());
        Assert.assertTrue(lock1.isLocked());
    }

    @Test
    public void unlockedTest() {
        lock1 = lock1.lock(process1).get();
        lock1 = lock1.unlock(process1).get();

        Assert.assertTrue(lock1.isValid());
        Assert.assertFalse(lock1.isLocked());
    }

    @Test
    public void reentrantTest() {
        lock1 = lock1.lock(process1).get();
        lock1 = lock1.lock(process1).get();
        lock1 = lock1.unlock(process1).get();
        lock1 = lock1.unlock(process1).get();

        Assert.assertTrue(lock1.isValid());
        Assert.assertFalse(lock1.isLocked());
    }

    @Test
    public void doubleUnlockTest() {
        lock1 = lock1.lock(process1).get();
        lock1 = lock1.unlock(process1).get();
        lock1 = lock1.unlock(process1).get();

        Assert.assertFalse(lock1.isValid());
    }

    @Test
    public void waitTest() {
        lock1 = lock1.lock(process1).get();
        lock1 = lock1.enterWait(process1).get();
        Assert.assertTrue(lock1.isValid());
    }

    @Test
    public void exitWaitWithoutNotifyTest() {
        lock1 = lock1.lock(process1).get();
        lock1 = lock1.enterWait(process1).get();
        Assert.assertFalse(lock1.exitWait(process1).isPresent());
    }

    @Test
    public void signalExitWaitUnlockTest() {
        lock1 = lock1.lock(process1).get();
        lock1 = lock1.enterWait(process1).get();

        lock1 = lock1.signalAll(process1).get();

        Assert.assertFalse(lock1.isLocked());
        Assert.assertTrue(lock1.isValid());

        lock1 = lock1.exitWait(process1).get();

        Assert.assertTrue(lock1.isValid());
        Assert.assertTrue(lock1.isLocked());

        lock1 = lock1.unlock(process1).get();

        Assert.assertTrue(lock1.isValid());
        Assert.assertFalse(lock1.isLocked());
    }

    @Test
    public void waitWithoutLockTest() {
        lock1 = lock1.enterWait(process1).get();
        Assert.assertFalse(lock1.isValid());
    }

    @Test
    public void twoLocksTest() {
        lock1 = lock1.lock(process1).get();
        lock2 = lock2.lock(process1).get();
        Assert.assertTrue(lock1.isValid());
        Assert.assertTrue(lock2.isValid());
    }

    @Test
    public void twoLockingTest() {
        lock1 = lock1.lock(process1).get();
        Assert.assertFalse(lock1.lock(process2).isPresent());

    }

    @Test
    public void lockUnlockLockTest() {
        lock1 = lock1.lock(process1).get();
        lock1 = lock1.unlock(process1).get();
        lock1 = lock1.lock(process2).get();
        Assert.assertTrue(lock1.isValid());
        Assert.assertTrue(lock1.isLocked());
    }

    @Test
    public void unlockWrongProcessTest() {
        lock1 = lock1.lock(process1).get();
        lock1 = lock1.unlock(process2).get();
        Assert.assertFalse(lock1.isValid());
    }

    @Test(expected = IllegalStateException.class)
    public void lockBetweenEnterWaitExitWaitTest() {
        lock1 = lock1.lock(process1).get(); // lock to enter blocked state
        lock1 = lock1.enterWait(process1).get();

        lock1.lock(process1);
        lock1 = lock1.exitWait(process1).get();
    }

    @Test(expected = IllegalStateException.class)
    public void unlockBetweenEnterWaitExitWaitTest() {
        lock1 = lock1.lock(process1).get(); // lock to enter blocked state
        lock1 = lock1.enterWait(process1).get();

        lock1.unlock(process1);
        lock1 = lock1.exitWait(process1).get();
    }
}
