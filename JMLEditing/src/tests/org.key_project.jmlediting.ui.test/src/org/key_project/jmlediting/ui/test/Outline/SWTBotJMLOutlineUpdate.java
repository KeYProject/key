package org.key_project.jmlediting.ui.test.Outline;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotEclipseEditor;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotView;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTree;
import org.eclipse.ui.IPageLayout;
import org.junit.AfterClass;
import org.junit.BeforeClass;
import org.key_project.jmlediting.core.profile.JMLPreferencesHelper;
import org.key_project.jmlediting.ui.test.utilities.JMLEditingUITestUtils;
import org.key_project.jmlediting.ui.test.utilities.JMLEditingUITestUtils.TestProject;
import org.key_project.jmlediting.ui.test.utilities.JMLEditingUITestUtils.TestProject.SaveGuarantee;
import org.key_project.util.test.util.TestUtilsUtil;

public class SWTBotJMLOutlineUpdate {
   
   
   
   private static SWTWorkbenchBot bot = new SWTWorkbenchBot();
   private static TestProject testProject;
   private static SWTBotEclipseEditor editor = null;

   private static final String PROJECT_NAME = "OutlineTest";
   private static final String PACKAGE_NAME = "test";
   private static final String CLASS_NAME = "OutlineTestClass";
   
   private static SWTBotTree tree;
   
   
   @BeforeClass
   public static void initProject() throws CoreException, InterruptedException {
      TestUtilsUtil.closeWelcomeView();
      TestUtilsUtil.findView(IPageLayout.ID_OUTLINE);
      testProject = JMLEditingUITestUtils.createProjectWithFile(bot, PROJECT_NAME, PACKAGE_NAME, CLASS_NAME, SaveGuarantee.NO_SAVE);

      JMLPreferencesHelper.setProjectJMLProfile(testProject.getProject().getProject(), JMLEditingUITestUtils.findReferenceProfile());
      
      testProject.restoreClassAndOpen();
      editor = testProject.getOpenedEditor();
      
      SWTBotView view = bot.viewByTitle("Outline");
       bot.menu("Window").click().menu("Show View").click().menu("Outline").click();
       view.show();
       tree = view.bot().tree();
       
   }
   
   @AfterClass
   public static void closeEditor() {
      editor.close();
   }

   
   
   
}
