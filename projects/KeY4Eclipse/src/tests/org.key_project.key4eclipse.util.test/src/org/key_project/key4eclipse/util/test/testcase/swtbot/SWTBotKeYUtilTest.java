package org.key_project.key4eclipse.util.test.testcase.swtbot;

import java.lang.reflect.InvocationTargetException;

import junit.framework.TestCase;

import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.jdt.core.IClasspathEntry;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.JavaCore;
import org.junit.Test;
import org.key_project.key4eclipse.util.eclipse.BundleUtil;
import org.key_project.key4eclipse.util.java.SwingUtil;
import org.key_project.key4eclipse.util.jdt.JDTUtil;
import org.key_project.key4eclipse.util.key.KeYUtil;
import org.key_project.key4eclipse.util.test.Activator;
import org.key_project.key4eclipse.util.test.util.TestUtilsUtil;
import org.key_project.swtbot.swing.bot.SwingBot;
import org.key_project.swtbot.swing.bot.SwingBotJDialog;
import org.key_project.swtbot.swing.bot.SwingBotJLabel;

import de.uka.ilkd.key.gui.MainWindow;

/**
 * SWT Bot tests for {@link KeYUtil}.
 * @author Martin Hentschel
 */
public class SWTBotKeYUtilTest extends TestCase {
    // TODO: Implement tests for the missing methods of class KeYUtil
    
    /**
     * Tests {@link KeYUtil#showErrorInKey(Throwable)}.
     */
    @Test
    public void testShowErrorInKey() throws InterruptedException, InvocationTargetException {
        final Exception exception = new Exception("Test Exception");
        // Open error dialog
        SwingUtil.invokeLater(new Runnable() {
            @Override
            public void run() {
                KeYUtil.showErrorInKey(exception);
            }
        });
        // Get and close error dialog
        SwingBotJDialog dialog = new SwingBot().jDialog("Error");
        assertTrue(dialog.isOpen());
        SwingBotJLabel label = dialog.bot().jLabel();
        assertEquals(exception.toString(), label.getText());
        dialog.close();
    }
    
    /**
     * Tests {@link KeYUtil#load(org.eclipse.core.resources.IResource)} and
     * {@link KeYUtil#loadAsync(org.eclipse.core.resources.IResource)}.
     */
    @Test
    public void testLoad() throws Exception {
        // Try to load general project in KeY.
        IProject project = TestUtilsUtil.createProject("SWTBotKeYUtilTest_testLoad_general");
        try {
            KeYUtil.load(project);
            fail("Loading general projects should not be possible.");
        }
        catch (Exception e) {
            assertTrue(e.getMessage(), e.getMessage().contains("The project \"" + project + "\" is no Java project."));
        }
        // Load java project with multiple source directories
        final IJavaProject javaProject = TestUtilsUtil.createJavaProject("SWTBotKeYUtilTest_testLoad_Java");
        BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/banking", javaProject.getProject().getFolder("src"));
        IFolder secondSrc = javaProject.getProject().getFolder("secondSrc");
        if (!secondSrc.exists()) {
            secondSrc.create(true, true, null);
        }
        IClasspathEntry[] oldEntries = javaProject.getRawClasspath();
        JDTUtil.addClasspathEntry(null, JavaCore.newSourceEntry(secondSrc.getFullPath()));
        try {
            KeYUtil.load(project);
            fail("Multiple source paths are not supported.");
        }
        catch (Exception e) {
            assertTrue(e.getMessage(), e.getMessage().contains("The project \"" + project + "\" is no Java project."));
        }
        javaProject.setRawClasspath(oldEntries, null);
        // Load java project with one source directory
        KeYUtil.loadAsync(javaProject.getProject());
        TestUtilsUtil.keyStartSelectedProofInProofManagementDiaolog();
        TestUtilsUtil.keyCheckProofs("JML operation contract [id: 0 / banking.LoggingPayCard::charge]", "JML operation contract [id: 0 / banking.LoggingPayCard::charge]");
        // Load second java project
        IJavaProject secondProject = TestUtilsUtil.createJavaProject("SWTBotKeYUtilTest_testLoad_Java2");
        BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/MCDemo", secondProject.getProject().getFolder("src"));
        KeYUtil.loadAsync(secondProject.getProject());
        TestUtilsUtil.keyStartSelectedProofInProofManagementDiaolog();
        TestUtilsUtil.keyCheckProofs("JML normal_behavior operation contract [id: 0 / MCDemo::inc]", "JML operation contract [id: 0 / banking.LoggingPayCard::charge]", "JML normal_behavior operation contract [id: 0 / MCDemo::inc]");
        // Open first project again to make sure that only the proof is selected again and no second proof environment is created
        KeYUtil.loadAsync(javaProject.getProject());
        TestUtilsUtil.keyGoToSelectedProofInProofManagementDiaolog();
        TestUtilsUtil.keyCheckProofs("JML operation contract [id: 0 / banking.LoggingPayCard::charge]", "JML operation contract [id: 0 / banking.LoggingPayCard::charge]", "JML normal_behavior operation contract [id: 0 / MCDemo::inc]");
        // Clear proof list
        KeYUtil.clearProofList(MainWindow.getInstance());
        TestCase.assertTrue(KeYUtil.isProofListEmpty(MainWindow.getInstance()));
        // Close main window
        TestUtilsUtil.keyCloseMainWindow();
    }
    
    /**
     * Tests {@link KeYUtil#openMainWindow()} and
     * {@link KeYUtil#openMainWindowAsync()}.
     */
    @Test
    public void testOpenMainWindow() throws InterruptedException, InvocationTargetException {
        // Open main window
        KeYUtil.openMainWindowAsync();
        // Close main window
        TestUtilsUtil.keyCloseMainWindow();
    }
}
