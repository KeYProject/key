package org.key_project.key4eclipse.resources.test.testcase.junit;

import org.junit.After;
import org.junit.Before;
import org.key_project.key4eclipse.resources.test.util.KeY4EclipseResourcesTestUtil;
import org.key_project.util.test.testcase.AbstractSetupTestCase;

import de.uka.ilkd.key.gui.configuration.ProofSettings;
import de.uka.ilkd.key.strategy.StrategyProperties;

public class AbstractResourceTest extends AbstractSetupTestCase {
   private boolean oldAutoBuildEnabled = true;
   
   private StrategyProperties spToRestore;
   
   private int maxStepsToRestore = -1;
   
   @Before
   @Override
   public void setUp() throws Exception {
      super.setUp();
      // Store current settings
      oldAutoBuildEnabled = KeY4EclipseResourcesTestUtil.enableAutoBuild(false);
      spToRestore = ProofSettings.DEFAULT_SETTINGS.getStrategySettings().getActiveStrategyProperties();
      maxStepsToRestore = ProofSettings.DEFAULT_SETTINGS.getStrategySettings().getMaxSteps();
      // Update settings
      StrategyProperties sp = new StrategyProperties();
      sp.setProperty(StrategyProperties.LOOP_OPTIONS_KEY, StrategyProperties.LOOP_INVARIANT);
      sp.setProperty(StrategyProperties.BLOCK_OPTIONS_KEY, StrategyProperties.BLOCK_EXPAND);
      sp.setProperty(StrategyProperties.METHOD_OPTIONS_KEY, StrategyProperties.METHOD_CONTRACT);
      sp.setProperty(StrategyProperties.QUERY_OPTIONS_KEY, StrategyProperties.QUERY_RESTRICTED);
      sp.setProperty(StrategyProperties.NON_LIN_ARITH_OPTIONS_KEY, StrategyProperties.NON_LIN_ARITH_DEF_OPS);
      sp.setProperty(StrategyProperties.AUTO_INDUCTION_OPTIONS_KEY, StrategyProperties.AUTO_INDUCTION_OFF);
      sp.setProperty(StrategyProperties.DEP_OPTIONS_KEY, StrategyProperties.DEP_OFF);
      sp.setProperty(StrategyProperties.QUERYAXIOM_OPTIONS_KEY, StrategyProperties.QUERYAXIOM_ON);
      sp.setProperty(StrategyProperties.SPLITTING_OPTIONS_KEY, StrategyProperties.SPLITTING_DELAYED);
      sp.setProperty(StrategyProperties.RETREAT_MODE_OPTIONS_KEY, StrategyProperties.RETREAT_MODE_NONE);
      sp.setProperty(StrategyProperties.STOPMODE_OPTIONS_KEY, StrategyProperties.STOPMODE_DEFAULT);
      sp.setProperty(StrategyProperties.QUANTIFIERS_OPTIONS_KEY, StrategyProperties.QUANTIFIERS_NON_SPLITTING_WITH_PROGS);
      ProofSettings.DEFAULT_SETTINGS.getStrategySettings().setActiveStrategyProperties(sp);
      ProofSettings.DEFAULT_SETTINGS.getStrategySettings().setMaxSteps(1000);
   }

   @After
   @Override
   public void tearDown() throws Exception {
      super.tearDown();
      // Restore old settings
      if (maxStepsToRestore >= 0) {
         ProofSettings.DEFAULT_SETTINGS.getStrategySettings().setMaxSteps(maxStepsToRestore);
      }
      if (spToRestore != null) {
         ProofSettings.DEFAULT_SETTINGS.getStrategySettings().setActiveStrategyProperties(spToRestore);
      }
      KeY4EclipseResourcesTestUtil.enableAutoBuild(oldAutoBuildEnabled);
   }
}
