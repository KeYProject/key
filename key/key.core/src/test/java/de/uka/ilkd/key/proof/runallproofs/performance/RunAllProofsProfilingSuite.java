package de.uka.ilkd.key.proof.runallproofs.performance;

import de.uka.ilkd.key.strategy.Strategy;
import de.uka.ilkd.key.strategy.feature.Feature;
import org.junit.runner.RunWith;
import org.junit.runners.Suite;
import org.junit.runners.Suite.SuiteClasses;

/**
 * Test suite that runs RunAllProofs and creates performance plots for functions
 * {@link Feature#computeCost} and {@link Strategy#instantiateApp}
 *
 * @author Kai Wallisch <kai.wallisch@ira.uka.de>
 */
@RunWith(Suite.class)
@SuiteClasses({ RunAllProofsTestWithComputeCostProfiling.class })
public class RunAllProofsProfilingSuite {
    // no members
}
