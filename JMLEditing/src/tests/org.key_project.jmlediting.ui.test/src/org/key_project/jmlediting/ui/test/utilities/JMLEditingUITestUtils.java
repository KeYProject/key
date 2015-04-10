package org.key_project.jmlediting.ui.test.utilities;

import static org.eclipse.swtbot.swt.finder.finders.UIThreadRunnable.syncExec;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jface.bindings.keys.KeyStroke;
import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.StyledText;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotEclipseEditor;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotView;
import org.eclipse.swtbot.swt.finder.exceptions.WidgetNotFoundException;
import org.eclipse.swtbot.swt.finder.matchers.AbstractMatcher;
import org.eclipse.swtbot.swt.finder.results.BoolResult;
import org.eclipse.swtbot.swt.finder.utils.Position;
import org.eclipse.swtbot.swt.finder.utils.SWTBotPreferences;
import org.eclipse.swtbot.swt.finder.waits.Conditions;
import org.eclipse.swtbot.swt.finder.waits.WaitForObjectCondition;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotShell;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTable;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTree;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTreeItem;
import org.eclipse.ui.texteditor.ITextEditor;
import org.hamcrest.Description;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.JMLProfileManagement;
import org.key_project.jmlediting.core.utilities.CommentLocator;
import org.key_project.jmlediting.core.utilities.CommentRange;
import org.key_project.jmlediting.core.utilities.ErrorTypes;
import org.key_project.jmlediting.ui.test.Activator;
import org.key_project.jmlediting.ui.test.utilities.JMLEditingUITestUtils.TestProject.SaveGuarantee;
import org.key_project.util.eclipse.BundleUtil;
import org.key_project.util.java.ArrayUtil;
import org.key_project.util.java.ObjectUtil;
import org.key_project.util.java.StringUtil;
import org.key_project.util.jdt.JDTUtil;
import org.key_project.util.test.util.TestUtilsUtil;

public class JMLEditingUITestUtils {
   public static SWTBotShell openJMLProfileProperties(final SWTWorkbenchBot bot, final IProject project) {
      TestUtilsUtil.openPropertiesPage(bot, project, "JML", "Profile");
      return bot.shell("Properties for " + project.getName());
   }

   public static SWTBotShell openJMLPreferencePage(final SWTWorkbenchBot bot) {
      return TestUtilsUtil.openPreferencePage(bot, "JML");
   }

   public static SWTBotShell openJMLProfilePreferencePage(final SWTWorkbenchBot bot) {
      TestUtilsUtil.openPreferencePage(bot, "JML", "Profile");
      return bot.shell("Preferences");
   }

   public static SWTBotShell openJMLColorsPreferencePage(final SWTWorkbenchBot bot) {
      TestUtilsUtil.openPreferencePage(bot, "JML", "Colors");
      return bot.shell("Preferences");
   }

   public static void validateProfileListSelection(
         final IJMLProfile expectedProfile, final SWTBotTable profileList) {
      // Now the global default should be selected
      // Unfortunately, we only get the names of the selection from swt bot
      final List<String> selectedProfiles = new ArrayList<String>(1);
      for (int i = 0; i < profileList.rowCount(); i++) {
         if (profileList.getTableItem(i).isChecked()) {
            selectedProfiles.add(profileList.getTableItem(i).getText());
         }
      }
      assertTrue("Not excately one profile selected",
            selectedProfiles.size() == 1);
      assertTrue("The selected profile does not match expected one",
            selectedProfiles.get(0).equals(expectedProfile.getName()));
   }

   public static String getHoverAtPosition(final SWTWorkbenchBot bot, final SWTBotEclipseEditor editor, final int line, final int column) {
      long originalTimeout = SWTBotPreferences.TIMEOUT;
      try {
         // Open hover
         editor.navigateTo(line, column);
         editor.pressShortcut(KeyStroke.getInstance(SWT.F2));
         // Set short timeout as information hover might not be shown
         SWTBotPreferences.TIMEOUT = 1000;
         // Search information shell which shows the hover
         WaitForObjectCondition<Shell> shell = Conditions.waitForShell(new AbstractMatcher<Shell>() {
            @Override
            public void describeTo(Description description) {
            }

            @Override
            protected boolean doMatch(final Object item) {
               if (item instanceof Shell) {
                  return syncExec(new BoolResult() {
                     @Override
                     public Boolean run() {
                        Shell shell = (Shell) item;
                        if (StringUtil.isEmpty(shell.getText())) {
                           Control[] children = shell.getChildren();
                           if (!ArrayUtil.isEmpty(children) &&
                               children[0] instanceof Composite) {
                              Control[] childChildren = ((Composite) children[0]).getChildren();
                              if (!ArrayUtil.isEmpty(childChildren) &&
                                  childChildren[0] instanceof StyledText) {
                                 return Boolean.TRUE;
                              }
                              else {
                                 return Boolean.FALSE;
                              }
                           }
                           else {
                              return Boolean.FALSE;
                           }
                        }
                        else {
                           return Boolean.FALSE;
                        }
                     }
                  });
               }
               else {
                  return Boolean.FALSE;
               }
            }
         });
         bot.waitUntilWidgetAppears(shell);
         SWTBotShell botShell = new SWTBotShell(shell.get(0));
         // Return shown hover text
         return botShell.bot().styledText().getText();
      }
      catch (WidgetNotFoundException e) {
         // Information shell not available, so no hover is shown
         return null;
      }
      finally {
         // Restore timeout
         SWTBotPreferences.TIMEOUT = originalTimeout;
      }
   }

   public static IJMLProfile findReferenceProfile() {
      for (final IJMLProfile profile : JMLProfileManagement.instance().getAvailableProfiles()) {
         if (profile.getIdentifier().equals("org.key_project.jmlediting.profile.jmlref")) {
            return profile;
         }
      }
      fail("Reference Profile not found");
      return null;
   }

   public static class TestProject {

      public static enum SaveGuarantee {
         NO_SAVE, SAVE_BUT_NO_CHANGES_LATER, NO_GUARANTEE;
      }

      private final SWTWorkbenchBot bot;
      private final String projectName;
      private final String packageName;
      private final String className;
      private final String classLocation;
      private SWTBotEclipseEditor openedEditor;
      private final IJavaProject project;
      private final IFolder testFolder;
      private final SaveGuarantee saveGuarantee;

      public TestProject(final SWTWorkbenchBot bot, final String projectName,
            final String packageName, final String className,
            final String classLoc, final SaveGuarantee guarantee)
            throws CoreException, InterruptedException {
         super();
         this.bot = bot;
         this.classLocation = classLoc;
         this.projectName = projectName;
         this.project = TestUtilsUtil.createJavaProject(this.projectName);
         this.packageName = packageName;
         this.className = className;
         this.saveGuarantee = guarantee;
         // Create folders for the package
         final IFolder srcFolder = this.project.getProject().getFolder("src");
         final String[] packageFolders = this.packageName.split("\\.");
         IFolder testFolder = srcFolder;
         for (final String folder : packageFolders) {
            testFolder = TestUtilsUtil.createFolder(testFolder, folder);
         }
         this.testFolder = testFolder;
         this.openedEditor = null;
      }

      public String getClassLocation() {
         return this.classLocation;
      }

      public String getClassName() {
         return this.className;
      }

      public String getPackageName() {
         return this.packageName;
      }

      public void copyData() throws CoreException {
         // Copy the class
         BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, this.classLocation, this.testFolder);
         TestUtilsUtil.waitForBuild();
      }

      public void restoreClassAndOpen() throws CoreException {
         // Check what to do in order to restore the content of the editor to
         // the given class
         // No editor -> copy class and restore
         // No guarantee -> "
         // SAVE_BUT_NO_CHANGES_LATER && not dirty -> "

         // Otherwise try to do something faster
         if (this.openedEditor != null
               && (this.saveGuarantee == SaveGuarantee.NO_SAVE || (this.saveGuarantee == SaveGuarantee.SAVE_BUT_NO_CHANGES_LATER && this.openedEditor
                     .isDirty()))) {
            // if NO_SAVE and not dirty -> everything fine
            // else revert to saved
            if (this.saveGuarantee == SaveGuarantee.SAVE_BUT_NO_CHANGES_LATER
                  || this.openedEditor.isDirty()) {
               this.bot.getDisplay().syncExec(new Runnable() {

                  @Override
                  public void run() {
                     ((ITextEditor) TestProject.this.openedEditor
                           .getReference().getEditor(true)).doRevertToSaved();
                  }
               });
            }
         }
         else {
            if (this.openedEditor != null) {
               this.openedEditor.close();
            }
            this.copyData();
            // Open the editor
            TestUtilsUtil.openEditor(getFile());
            this.openedEditor = this.bot.activeEditor().toTextEditor();
         }
      }
      
      public IFile getFile() {
         return testFolder.getFile(this.className + JDTUtil.JAVA_FILE_EXTENSION_WITH_DOT);
      }

      public IJavaProject getProject() {
         return this.project;
      }

      public SWTBotEclipseEditor getOpenedEditor() {
         return this.openedEditor;
      }

   }

   /**
    * Does the same as
    * {@link JMLEditingUITestUtils#createProjectWithFileAndOpen(SWTWorkbenchBot, String, String, String, String)}
    * but implies the location of the class file. The source file to copy should
    * be located in data/template/CLASSNAME.java
    *
    * @param bot
    *           the bot to use
    * @param projectName
    *           the project name
    * @param packageName
    *           the package name
    * @param className
    *           the class name
    * @return the project and opened editor
    * @throws CoreException
    * @throws InterruptedException
    */
   public static TestProject createProjectWithFile(final SWTWorkbenchBot bot,
         final String projectName, final String packageName,
         final String className, final SaveGuarantee guarantee)
         throws CoreException, InterruptedException {
      return createProjectWithFile(bot, projectName, packageName, className,
            "data/template/" + className + JDTUtil.JAVA_FILE_EXTENSION_WITH_DOT, guarantee);
   }

   /**
    * Creates a new Java Projects and copies a class into the project. The it
    * opens to class in the editor. The guarantee with respect to saving the
    * content of the opened editor influences the test speed. The higher the
    * guarantee is, the faster the test can be because the editor does not neet
    * be reopened that many times.
    *
    * @param bot
    *           the bot to use
    * @param projectName
    *           the name for the new project
    * @param packageName
    *           the package name of the class (with dots)
    * @param className
    *           the class name
    * @param classLoc
    *           the location where the class source file is located and from
    *           which it should be copied
    * @param the
    *           guarantee the user of the created TestProject gives with regards
    *           to saving the content of the opened editor
    * @return an object of type {@link TestProject} which contains the editor
    *         and the project
    * @throws CoreException
    * @throws InterruptedException
    */
   public static TestProject createProjectWithFile(final SWTWorkbenchBot bot,
         final String projectName, final String packageName,
         final String className, final String classLoc,
         final SaveGuarantee guarantee) throws CoreException,
         InterruptedException {

      return new TestProject(bot, projectName, packageName, className,
            classLoc, guarantee);
   }

   /**
    * Searches for all error markers which are visibile in the problems view.
    *
    * @param bot
    *           the bot to use
    * @return all tree items in the problems view, which belong to an error
    */
   public static SWTBotTreeItem[] getAllErrorItems(final SWTWorkbenchBot bot) {

      // Search the view
      SWTBotView problemsView = null;
      for (final SWTBotView view : bot.views()) {
         if ("Problems".equals(view.getTitle())) {
            problemsView = view;
         }
      }
      if (problemsView == null) {
         // Could try to open view by menu
         // But it is open in our product
         return new SWTBotTreeItem[0];
      }
      // Navigate to the Errors item
      final SWTBotTree problemTree = problemsView.bot().tree();
      SWTBotTreeItem errorItem = null;
      for (final SWTBotTreeItem item : problemTree.getAllItems()) {
         if (item.getText().startsWith("Errors")) {
            errorItem = item;
            break;
         }
      }
      if (errorItem == null) {
         return new SWTBotTreeItem[0];
      }
      errorItem.expand();

      return errorItem.getItems();
   }

   /**
    * Returns all lines annotated with an error marker specified by {@link ErrorTypes}.
    * @param file The {@link IFile} to get its error lines.
    * @return The found error lines.
    * @throws CoreException Occurred Exception.
    */
   public static List<Integer> getAllErrorLines(final IFile file) throws CoreException {
      List<Integer> result = new LinkedList<Integer>();
      for (ErrorTypes type : ErrorTypes.values()) {
         IMarker[] markers = file.findMarkers(type.getId(), true, IResource.DEPTH_INFINITE);
         if (!ArrayUtil.isEmpty(markers)) {
            for (IMarker marker : markers) {
               String line = ObjectUtil.toString(marker.getAttribute(IMarker.LINE_NUMBER)); 
               result.add(Integer.valueOf(line));
            }
         }
      }
      return result;
   }

   public static Position getLineAndColumn(final int offset,
         final SWTBotEclipseEditor editor) {
      int lineOffset = 0;
      for (int line = 0; line < editor.getLineCount(); line++) {
         int nextLineOffset = lineOffset + editor.getLines().get(line).length();
         // Check new line characters
         if (editor.getText().length() > nextLineOffset) {
            final char newLine1 = editor.getText().charAt(nextLineOffset);
            final char newLine2 = editor.getText().charAt(nextLineOffset + 1);
            if (newLine1 == '\n' && newLine2 == 'r') {
               nextLineOffset += 2;
            }
            else {
               // One new line at least
               nextLineOffset++;
            }
         }
         // Check whether offset is in line
         if (offset < nextLineOffset) {
            return new Position(line, offset - lineOffset);
         }
         lineOffset = nextLineOffset;
      }
      throw new IndexOutOfBoundsException("Offset not in text");
   }

   public static List<CommentRange> getAllJMLCommentsInEditor(final SWTBotEclipseEditor editor) {
      return new CommentLocator(editor.getText()).findJMLCommentRanges();
   }
}
