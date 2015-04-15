package org.key_project.key4eclipse.common.ui.test.testcase.swtbot;

import junit.framework.TestCase;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jface.dialogs.IDialogConstants;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.swt.finder.waits.Conditions;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotShell;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTable;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTree;
import org.junit.Test;
import org.key_project.key4eclipse.common.ui.property.KeYIncludesPropertyPage;
import org.key_project.key4eclipse.common.ui.test.Activator;
import org.key_project.key4eclipse.starter.core.property.KeYPathEntry;
import org.key_project.key4eclipse.starter.core.property.KeYResourceProperties;
import org.key_project.key4eclipse.starter.core.property.KeYPathEntry.KeYPathEntryKind;
import org.key_project.util.collection.ImmutableSet;
import org.key_project.util.eclipse.BundleUtil;
import org.key_project.util.jdt.JDTUtil;
import org.key_project.util.test.util.TestUtilsUtil;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;
import de.uka.ilkd.key.util.HelperClassForTests;

/**
 * SWTBot tests for {@link KeYIncludesPropertyPage}.
 * @author Martin Hentschel
 */
public class SWTBotKeYIncludesPropertyPageTest extends TestCase {
   /**
    * Tests some scenarios in the {@link KeYIncludesPropertyPage} with help of the example {@code includeExample}.
    * @throws Exception
    */
   @Test
   public void testIncludeExample() throws Exception {
      // Close welcome view
      SWTWorkbenchBot bot = new SWTWorkbenchBot();
      TestUtilsUtil.closeWelcomeView(bot);
      // Create test project (no includes set)
      IJavaProject project = TestUtilsUtil.createJavaProject("SWTBotKeYIncludesPropertyPageTest_testIncludeExample");
      IFolder src = project.getProject().getFolder(JDTUtil.getSourceFolderName());
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/includeExample/src", src);
      IFolder rules = TestUtilsUtil.createFolder(project.getProject(), "rules");
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/includeExample/rules", rules);
      IFile myRules = rules.getFile("MyRules.key");
      // Ensure that proof is initially open without includes set
      assertProof(project, false);
      // Set include
      SWTBotShell propertiesShell = TestUtilsUtil.openPropertiesPage(bot, project.getProject(), "KeY", "Includes");
      assertEntries(propertiesShell);
      propertiesShell.bot().button("Add Workspace F&ile").click();
      SWTBotShell addShell = propertiesShell.bot().shell("Select class path file to add");
      SWTBotTree addTree = addShell.bot().tree();
      TestUtilsUtil.selectInTree(addTree, project.getProject().getName(), rules.getName(), myRules.getName());
      addShell.bot().button(IDialogConstants.OK_LABEL).click();
      addShell.bot().waitUntil(Conditions.shellCloses(addShell));
      assertEntries(propertiesShell, myRules);
      propertiesShell.bot().button(IDialogConstants.OK_LABEL).click();
      propertiesShell.bot().waitUntil(Conditions.shellCloses(propertiesShell));
      assertProof(project, true);
      // Test removing and canceling the properties
      propertiesShell = TestUtilsUtil.openPropertiesPage(bot, project.getProject(), "KeY", "Includes");
      assertEntries(propertiesShell, myRules);
      propertiesShell.bot().table().select(0);
      propertiesShell.bot().button("&Remove").click();
      assertEntries(propertiesShell);
      propertiesShell.bot().button(IDialogConstants.CANCEL_LABEL).click();
      propertiesShell.bot().waitUntil(Conditions.shellCloses(propertiesShell));
      assertProof(project, true);
      // Test default and apply
      propertiesShell = TestUtilsUtil.openPropertiesPage(bot, project.getProject(), "KeY", "Includes");
      assertEntries(propertiesShell, myRules);
      propertiesShell.bot().button("Restore Defaults").click();
      assertEntries(propertiesShell);
      propertiesShell.bot().button("Apply").click();
      propertiesShell.bot().button(IDialogConstants.CANCEL_LABEL).click();
      propertiesShell.bot().waitUntil(Conditions.shellCloses(propertiesShell));
      assertProof(project, false);
   }
   
   /**
    * Ensures that the correct entries in the table are shown.
    * @param propertiesShell The {@link SWTBotShell} of the properties dialog.
    * @param expectedResources The expected entries.
    */
   private void assertEntries(SWTBotShell propertiesShell, IResource... expectedResources) {
      SWTBotTable entriesTable = propertiesShell.bot().table();
      assertEquals(expectedResources.length, entriesTable.rowCount());
      for (int i = 0; i < expectedResources.length; i++) {
         Object data = TestUtilsUtil.getTableItemData(entriesTable.getTableItem(i));
         assertTrue(data instanceof KeYPathEntry);
         KeYPathEntry entry = (KeYPathEntry) data;
         assertEquals(KeYPathEntryKind.WORKSPACE, entry.getKind());
         assertEquals(expectedResources[i].getFullPath().toString(), entry.getPath());
      }
   }

   /**
    * Ensures the correct proof result.
    * @param javaProject The {@link IJavaProject} which provides souce code and includes.
    * @param expectedCloseState The expected proof state.
    * @throws Exception Occurred Exception.
    */
   protected void assertProof(IJavaProject javaProject, boolean expectedCloseState) throws Exception {
      IProject project = javaProject.getProject();
      Proof proof = null;
      KeYEnvironment<?> environment = KeYEnvironment.load(KeYResourceProperties.getSourceClassPathLocation(project), 
                                                          KeYResourceProperties.getKeYClassPathEntries(project), 
                                                          KeYResourceProperties.getKeYBootClassPathLocation(project), 
                                                          KeYResourceProperties.getKeYIncludes(project));
      
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
