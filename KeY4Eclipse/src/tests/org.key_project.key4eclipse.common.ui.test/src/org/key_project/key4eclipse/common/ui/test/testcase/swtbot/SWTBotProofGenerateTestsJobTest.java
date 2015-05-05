package org.key_project.key4eclipse.common.ui.test.testcase.swtbot;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.junit.Test;
import org.key_project.key4eclipse.common.ui.test.Activator;
import org.key_project.key4eclipse.common.ui.testGeneration.ProofGenerateTestsJob;
import org.key_project.util.eclipse.BundleUtil;
import org.key_project.util.eclipse.ResourceUtil;
import org.key_project.util.java.StringUtil;
import org.key_project.util.jdt.JDTUtil;
import org.key_project.util.test.util.TestUtilsUtil;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.WindowUserInterfaceControl;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.smt.SolverType;
import de.uka.ilkd.key.smt.test.TestZ3;
import de.uka.ilkd.key.smt.testgen.AbstractTestGenerator;

/**
 * SWTBot tests for {@link ProofGenerateTestsJob}.
 * 
 * The Z3 solver path ({@code z3SolverPath}) needs to be set, e.g. 
 * {@code -Dz3SolverPath=D:\Forschung\Tools\z3-4.3.0-x64\bin\z3.exe}
 * @author Martin Hentschel
 */
public class SWTBotProofGenerateTestsJobTest extends AbstractGenerateTestsJobTest {
   /**
    * Tests the test generation with the magic42 example.
    */
   @Test
   public void testTestGeneration() throws Exception {
      SWTWorkbenchBot bot = new SWTWorkbenchBot();
      KeYEnvironment<WindowUserInterfaceControl> env = null;
      try {
         TestUtilsUtil.closeWelcomeView(bot);
         bot.closeAllEditors();
         // Ensure that test generation is possible
         SolverType type = SolverType.Z3_CE_SOLVER;
         String solverPathProperty = System.getProperty(TestZ3.SYSTEM_PROPERTY_SOLVER_PATH);
         if (!StringUtil.isTrimmedEmpty(solverPathProperty)) {
            type.setSolverCommand(solverPathProperty);
         }
         assertTrue(AbstractTestGenerator.isSolverAvailable());
         // Create test project
         IJavaProject project = TestUtilsUtil.createJavaProject("SWTBotProofGenerateTestsJobTest_testTestGeneration");
         IFolder src = project.getProject().getFolder(JDTUtil.getSourceFolderName());
         BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/magic42", src);
         TestUtilsUtil.waitForBuild();
         IFile proofFile = src.getFile("IntegerUtil.proof");
         assertTrue(proofFile.exists());
         // Open Proof
         env = WindowUserInterfaceControl.loadInMainWindow(ResourceUtil.getLocation(proofFile), null, null, null, false);
         KeYMediator mediator = env.getUi().getMediator();
         assertNotNull(mediator);
         Proof proof = env.getLoadedProof();
         Proof mediatorProof = mediator.getSelectedProof();
         assertSame(proof, mediatorProof);
         Node mediatorNode = mediator.getSelectedNode();
         Goal mediatorGoal = mediator.getSelectedGoal();
         // Generate test cases
         ProofGenerateTestsJob job = new ProofGenerateTestsJob(project.getProject(), proof, env.getUi());
         job.schedule();
         TestUtilsUtil.waitForJobs();
         // Test generated stuff
         assertTestProjectAndOpenedEditor(bot, project, proof.name().toString());
         // Ensure that same objects are still selected in the mediator
         assertFalse(proof.isDisposed());
         assertSame(mediatorProof, mediator.getSelectedProof());
         assertSame(mediatorNode, mediator.getSelectedNode());
         assertSame(mediatorGoal, mediator.getSelectedGoal());
      }
      finally {
         if (env != null) {
            env.dispose();
         }
         bot.closeAllEditors();
      }
   }
}
