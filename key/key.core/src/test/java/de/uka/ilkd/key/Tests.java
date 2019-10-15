package de.uka.ilkd.key;

import de.uka.ilkd.key.AutoSuite.AutoSuiteExclude;
import de.uka.ilkd.key.AutoSuite.AutoSuitePath;
import de.uka.ilkd.key.parser.TestParallelParsing;
import de.uka.ilkd.key.proof.proverules.ProveRulesTest;
import de.uka.ilkd.key.proof.runallproofs.RunAllProofsFunctional;
import de.uka.ilkd.key.proof.runallproofs.RunAllProofsInfFlow;
import de.uka.ilkd.key.proof.runallproofs.RunAllProofsTest;
import de.uka.ilkd.key.proof.runallproofs.performance.RunAllProofsTestWithComputeCostProfiling;
import de.uka.ilkd.key.smt.test.TestCvc4;
import org.junit.runner.RunWith;
import org.key_project.util.testcategories.Interactive;
import org.key_project.util.testcategories.Performance;

@RunWith(AutoSuite.class)
@AutoSuitePath("build/classes/java/test/")
@AutoSuiteExclude(
        categories = { Interactive.class, Performance.class },
        classes = {
                ProveRulesTest.class,
                RunAllProofsTest.class,
                RunAllProofsFunctional.class,
                RunAllProofsTestWithComputeCostProfiling.class,
                RunAllProofsInfFlow.class,
                TestParallelParsing.class,
                TestCvc4.class
        }
)
public class Tests {
}


