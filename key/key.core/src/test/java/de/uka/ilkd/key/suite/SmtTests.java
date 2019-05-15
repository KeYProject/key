package de.uka.ilkd.key.suite;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;

@RunWith(Suite.class)
@Suite.SuiteClasses({de.uka.ilkd.key.smt.test.TestSimplify.class,
        de.uka.ilkd.key.smt.test.TestZ3.class,
        de.uka.ilkd.key.smt.test.TestYices.class,
        de.uka.ilkd.key.smt.test.TestCvc3.class
        //, de.uka.ilkd.key.smt.test.TestCvc4.class  //commented out as test take too long
})
public class SmtTests {
}