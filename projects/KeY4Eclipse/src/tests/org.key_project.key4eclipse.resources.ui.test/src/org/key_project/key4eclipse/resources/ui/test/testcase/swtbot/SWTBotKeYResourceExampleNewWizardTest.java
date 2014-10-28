package org.key_project.key4eclipse.resources.ui.test.testcase.swtbot;

import junit.framework.TestCase;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.Path;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.JavaCore;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotEditor;
import org.eclipse.swtbot.swt.finder.waits.Conditions;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotShell;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotText;
import org.junit.Test;
import org.key_project.key4eclipse.resources.projectinfo.MethodInfo;
import org.key_project.key4eclipse.resources.projectinfo.PackageInfo;
import org.key_project.key4eclipse.resources.projectinfo.ProjectInfo;
import org.key_project.key4eclipse.resources.projectinfo.ProjectInfoManager;
import org.key_project.key4eclipse.resources.projectinfo.TypeInfo;
import org.key_project.key4eclipse.resources.test.util.KeY4EclipseResourcesTestUtil;
import org.key_project.key4eclipse.resources.ui.wizard.KeYResourceExampleNewWizard;
import org.key_project.util.test.util.TestUtilsUtil;

/**
 * SWTBot tests for {@link KeYResourceExampleNewWizard}.
 * @author Martin Hentschel
 */
public class SWTBotKeYResourceExampleNewWizardTest extends TestCase {
   /**
    * Tests the created project.
    */
   @Test
   public void testCreatedProject() throws Exception {
      SWTWorkbenchBot bot = new SWTWorkbenchBot();
      // Open Java perspective
      TestUtilsUtil.openJavaPerspective();
      // Open new example wizard
      TestUtilsUtil.menuClick(bot, "File", "New", "Example...");
      SWTBotShell shell = bot.shell("New Example");
      //  Open Banking Example wizard
      TestUtilsUtil.selectInTree(shell.bot().tree(), "KeY", "KeY Project Example");
      TestUtilsUtil.clickDirectly(shell.bot(), "Next >");
      // Define project name
      SWTBotText text = shell.bot().text(0);
      text.setText("SWTBotKeYResourceExampleNewWizardTest");
      // Finish wizard
      TestUtilsUtil.clickDirectly(shell.bot(), "Finish");
      shell.bot().waitUntil(Conditions.shellCloses(shell));
      KeY4EclipseResourcesTestUtil.waitBuild();
      // Test created project
      IProject project = ResourcesPlugin.getWorkspace().getRoot().getProject("SWTBotKeYResourceExampleNewWizardTest");
      assertTrue(project.exists());
      assertTrue(project.isOpen());
      IJavaProject javaProject = JavaCore.create(project);
      assertNotNull(javaProject);
      assertTrue(javaProject.exists());
      // Test opened editor
      SWTBotEditor editor = bot.activeEditor();
      assertEquals(project.getFile(new Path("src/IntegerUtil.java")), editor.getReference().getEditorInput().getAdapter(IFile.class));
      editor.close();
      // Test verification result
      ProjectInfo projectInfo = ProjectInfoManager.getInstance().getProjectInfo(project);
      PackageInfo packageInfo = projectInfo.getPackage(PackageInfo.DEFAULT_NAME);
      TypeInfo integerInfo = packageInfo.getType("IntegerUtil");
      MethodInfo addInfo = integerInfo.getMethod("add(int, int)");
      assertEquals(Boolean.TRUE, addInfo.getContract(0).checkProofClosed());
      MethodInfo subInfo = integerInfo.getMethod("sub(int, int)");
      assertEquals(Boolean.FALSE, subInfo.getContract(0).checkProofClosed());
      TypeInfo recursionInfo = packageInfo.getType("MultipleRecursion");
      MethodInfo aInfo = recursionInfo.getMethod("a()");
      assertEquals(Boolean.TRUE, aInfo.getContract(0).checkProofClosed());
      assertEquals(1, aInfo.getContract(0).checkProofRecursionCycle().size());
      MethodInfo bInfo = recursionInfo.getMethod("b()");
      assertEquals(Boolean.TRUE, bInfo.getContract(0).checkProofClosed());
      assertEquals(1, bInfo.getContract(0).checkProofRecursionCycle().size());
   }
}
