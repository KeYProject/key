package org.key_project.key4eclipse.common.ui.test.testcase.swtbot;

import junit.framework.TestCase;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jface.dialogs.IDialogConstants;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.swt.finder.waits.Conditions;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotShell;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTableItem;
import org.junit.Test;
import org.key_project.key4eclipse.common.ui.test.Activator;
import org.key_project.key4eclipse.common.ui.wizard.ExportProjectFileWizard;
import org.key_project.key4eclipse.starter.core.property.KeYPathEntry;
import org.key_project.key4eclipse.starter.core.property.KeYPathEntry.KeYPathEntryKind;
import org.key_project.key4eclipse.starter.core.property.KeYResourceProperties;
import org.key_project.key4eclipse.starter.core.property.KeYResourceProperties.UseBootClassPathKind;
import org.key_project.util.collection.ImmutableSet;
import org.key_project.util.eclipse.BundleUtil;
import org.key_project.util.eclipse.ResourceUtil;
import org.key_project.util.java.CollectionUtil;
import org.key_project.util.jdt.JDTUtil;
import org.key_project.util.test.util.TestUtilsUtil;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;
import de.uka.ilkd.key.util.HelperClassForTests;

/**
 * SWTBot tests for the {@link ExportProjectFileWizard}.
 * @author Martin Hentschel
 */
public class SWTBotExportProjectFileWizardTest extends TestCase {
   /**
    * Ensures that the exported file can be opened by KeY.
    */
   @Test
   public void testExportedFile() throws Exception {
      // Close welcome view
      SWTWorkbenchBot bot = new SWTWorkbenchBot();
      TestUtilsUtil.closeWelcomeView(bot);
      // Create test project (no includes set)
      IJavaProject project = TestUtilsUtil.createJavaProject("SWTBotExportProjectFileWizardTest_testExportedFile");
      IFolder src = project.getProject().getFolder(JDTUtil.getSourceFolderName());
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/exportKeYFileTest/src", src);
      IFolder rules = TestUtilsUtil.createFolder(project.getProject(), "rules");
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/exportKeYFileTest/rules", rules);
      IFile copyRules = rules.getFile("CopyMyRules.key");
      IFile myRules = rules.getFile("MyRules.key");
      IFolder boot = TestUtilsUtil.createFolder(project.getProject(), "boot");
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/exportKeYFileTest/boot", boot);
      IFolder classPath1 = TestUtilsUtil.createFolder(project.getProject(), "classPath1");
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/exportKeYFileTest/classPath1", classPath1);
      IFolder classPath2 = TestUtilsUtil.createFolder(project.getProject(), "classPath2");
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/exportKeYFileTest/classPath2", classPath2);
      KeYResourceProperties.setBootClassPath(project.getProject(), UseBootClassPathKind.WORKSPACE, boot.getFullPath().toString());
      KeYResourceProperties.setClassPathEntries(project.getProject(), CollectionUtil.toList(new KeYPathEntry(KeYPathEntryKind.WORKSPACE, classPath1.getFullPath().toString()), new KeYPathEntry(KeYPathEntryKind.WORKSPACE, classPath2.getFullPath().toString())));
      KeYResourceProperties.setIncludeEntries(project.getProject(), CollectionUtil.toList(new KeYPathEntry(KeYPathEntryKind.WORKSPACE, copyRules.getFullPath().toString()), new KeYPathEntry(KeYPathEntryKind.WORKSPACE, myRules.getFullPath().toString())));
      // Open export wizard
      bot.menu("File").menu("Export...").click();
      SWTBotShell wizardShell = bot.shell("Export");
      // Select export wizard
      TestUtilsUtil.selectInTree(wizardShell.bot().tree(), "KeY", "Project.key File");
      TestUtilsUtil.clickDirectly(wizardShell.bot().button(IDialogConstants.NEXT_LABEL));
      // Perform export
      SWTBotTableItem item = wizardShell.bot().table().getTableItem(project.getProject().getName());
      item.check();
      TestUtilsUtil.clickDirectly(wizardShell.bot().button(IDialogConstants.FINISH_LABEL));
      wizardShell.bot().waitUntil(Conditions.shellCloses(wizardShell));
      // Test created file
      IFile projectFile = project.getProject().getFile("project.key");
      assertTrue(projectFile.exists());
      // Load file
      assertProof(projectFile, true);
   }

   /**
    * Ensures the correct proof result.
    * @param projectFile The {@link IFile} to load.
    * @param expectedCloseState The expected proof state.
    * @throws Exception Occurred Exception.
    */
   protected void assertProof(IFile projectFile, boolean expectedCloseState) throws Exception {
      Proof proof = null;
      KeYEnvironment<?> environment = KeYEnvironment.load(ResourceUtil.getLocation(projectFile), 
                                                          null,
                                                          null,
                                                          null);
      
      try {
         IProgramMethod pm = HelperClassForTests.searchProgramMethod(environment.getServices(), "Main", "magic");
         ImmutableSet<FunctionalOperationContract> contracts = environment.getSpecificationRepository().getOperationContracts(pm.getContainerType(), pm);
         assertEquals(1, contracts.size());
         FunctionalOperationContract contract = contracts.iterator().next();
         // Create proof
         proof = environment.createProof(contract.createProofObl(environment.getInitConfig()));
         assertNotNull(proof);
         // Start auto mode
         environment.getUi().getProofControl().startAndWaitForAutoMode(proof);
         // Test result
         assertEquals(expectedCloseState, proof.closed());
      }
      finally {
         if (proof != null) {
            proof.dispose();
         }
         environment.dispose();
      }
   }
}
