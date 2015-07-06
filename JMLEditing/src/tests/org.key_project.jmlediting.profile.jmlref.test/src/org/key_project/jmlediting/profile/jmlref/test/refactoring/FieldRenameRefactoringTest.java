package org.key_project.jmlediting.profile.jmlref.test.refactoring;

import org.eclipse.core.resources.IFolder;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jface.dialogs.IDialogConstants;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotEclipseEditor;
import org.eclipse.swtbot.swt.finder.SWTBot;
import org.eclipse.swtbot.swt.finder.matchers.WidgetMatcherFactory;
import org.eclipse.swtbot.swt.finder.waits.Conditions;
import org.eclipse.swtbot.swt.finder.waits.ICondition;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotShell;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTree;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTreeItem;
import org.hamcrest.Matcher;
import org.junit.AfterClass;
import org.junit.BeforeClass;
import org.junit.Test;
import org.key_project.jmlediting.core.profile.JMLPreferencesHelper;
import org.key_project.jmlediting.profile.jmlref.test.Activator;
import org.key_project.util.eclipse.BundleUtil;
import org.key_project.util.jdt.JDTUtil;
import org.key_project.util.test.util.TestUtilsUtil;

public class FieldRenameRefactoringTest<WaitForShell> {
    
    private static final String PROJECT_NAME = "JMLRefactoringRenameTest";
    private static final String PACKAGE_NAME = "test";
    private static final String CLASS_NAME = "TestClass1";
    //private static final String CLASS_NAME_GOAL = "TestClass1Solution";

    private static final SWTWorkbenchBot bot = new SWTWorkbenchBot();
       
    private static SWTBotEclipseEditor editor;

    @BeforeClass
    public static void initProject() throws CoreException, InterruptedException {
        TestUtilsUtil.closeWelcomeView();
                
        final IJavaProject project = TestUtilsUtil.createJavaProject(PROJECT_NAME);
        
        IFolder srcFolder = project.getProject().getFolder(JDTUtil.getSourceFolderName());
        IFolder testFolder = TestUtilsUtil.createFolder(srcFolder, PACKAGE_NAME);
        
        BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data\\template\\refactoringRenameTest", testFolder);
        
        TestUtilsUtil.waitForBuild();
        
        JMLPreferencesHelper.setProjectJMLProfile(project.getProject(), JMLPreferencesHelper.getDefaultJMLProfile());
        
        TestUtilsUtil.openEditor(testFolder.getFile(CLASS_NAME + JDTUtil.JAVA_FILE_EXTENSION_WITH_DOT));

    }
 
    @Test
    public void test1() throws InterruptedException {  
 
        // Go to the outline and select the field named "balance"
        SWTBotTree tree = TestUtilsUtil.getOutlineView(bot).bot().tree(); 
        SWTBotTreeItem outlineItem = tree.getTreeItem(CLASS_NAME); 
        SWTBotTreeItem fieldToRename = outlineItem.getNode("balance : int"); 
        fieldToRename.select().pressShortcut(SWT.ALT | SWT.SHIFT, 'R');
        
        //bot.sleep(1000);
        //SWTBotTreeItem fieldToRename = TestUtilsUtil.selectInTree(tree, 1, 1);
        //TestUtilsUtil.waitUntilSelected(bot, tree, fieldToRename);
     
        // Wait for refactoring dialog        
        Matcher<Shell> matcher = WidgetMatcherFactory.withText("Rename Field");
        ICondition waitForRefactoringDialog = Conditions.waitForShell(matcher);     
        bot.waitUntilWidgetAppears(waitForRefactoringDialog);
                
        // change variable name
        SWTBotShell renameDialog = bot.activeShell();      
        SWTBot dialogBot = renameDialog.bot();
        dialogBot.textWithLabel("New name:").setText("aVeryLongNewName");    
        System.out.println("Starting refactoring");
        dialogBot.button(IDialogConstants.OK_ID).click();
        
        // Compare content of editor after refactoring to its solution
        bot.waitUntil(Conditions.shellCloses(renameDialog));
        editor = bot.activeEditor().toTextEditor();
        String content = editor.getText();
        System.out.println(content);      
        //bot.sleep(100000);          
        
        //String solution = "";
        //assertEquals(solution,content);
    }
    
    @AfterClass
    public static void closeEditor() {
       editor.close();
    }
}
