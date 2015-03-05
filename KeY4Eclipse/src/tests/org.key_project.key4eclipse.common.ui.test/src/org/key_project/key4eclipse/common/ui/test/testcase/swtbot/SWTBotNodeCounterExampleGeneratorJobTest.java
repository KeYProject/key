package org.key_project.key4eclipse.common.ui.test.testcase.swtbot;

import junit.framework.TestCase;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotShell;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTree;
import org.junit.Test;
import org.key_project.key4eclipse.common.ui.counterExample.NodeCounterExampleGeneratorJob;
import org.key_project.key4eclipse.common.ui.test.Activator;
import org.key_project.util.eclipse.BundleUtil;
import org.key_project.util.eclipse.ResourceUtil;
import org.key_project.util.java.StringUtil;
import org.key_project.util.jdt.JDTUtil;
import org.key_project.util.test.util.TestUtilsUtil;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.smt.SolverType;
import de.uka.ilkd.key.smt.test.TestZ3;
import de.uka.ilkd.key.smt.testgen.AbstractTestGenerator;

/**
 * SWTBot tests for {@link NodeCounterExampleGeneratorJob}.
 * 
 * The Z3 solver path ({@code z3SolverPath}) needs to be set, e.g. 
 * {@code -Dz3SolverPath=D:\Forschung\Tools\z3-4.3.0-x64\bin\z3.exe}
 * @author Martin Hentschel
 */
public class SWTBotNodeCounterExampleGeneratorJobTest extends TestCase {
   /**
    * Tests the test generation with the magic42 example.
    */
   @Test
   public void testCounterExampleGeneration() throws Exception {
      SWTWorkbenchBot bot = new SWTWorkbenchBot();
      KeYEnvironment<?> env = null;
      try {
         TestUtilsUtil.closeWelcomeView(bot);
         // Ensure that test generation is possible
         SolverType type = SolverType.Z3_CE_SOLVER;
         String solverPathProperty = System.getProperty(TestZ3.SYSTEM_PROPERTY_SOLVER_PATH);
         if (!StringUtil.isTrimmedEmpty(solverPathProperty)) {
            type.setSolverCommand(solverPathProperty);
         }
         assertTrue(AbstractTestGenerator.isSolverAvailable());
         // Create test project
         IJavaProject project = TestUtilsUtil.createJavaProject("SWTBotNodeCounterExampleGeneratorJobTest_testCounterExampleGeneration");
         IFolder src = project.getProject().getFolder(JDTUtil.getSourceFolderName());
         BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/counterExample", src);
         TestUtilsUtil.waitForBuild();
         IFile proofFile = src.getFile("CounterExample.proof");
         assertTrue(proofFile.exists());
         // Open proof
         env = KeYEnvironment.load(ResourceUtil.getLocation(proofFile), null, null);
         Goal goal = env.getLoadedProof().openGoals().head();
         // Generate test cases
         NodeCounterExampleGeneratorJob job = new NodeCounterExampleGeneratorJob(env.getUi(), goal.node());
         job.schedule();
         TestUtilsUtil.waitForJobs();
         // Test generated stuff
         SWTBotShell shell = bot.shell("SMT Counterexample Search");
         SWTBotTree propertiesTree = shell.bot().tree();
         assertEquals(2, propertiesTree.rowCount());
         shell.close();
      }
      finally {
         if (env != null) {
            env.dispose();
         }
      }
   }
}
