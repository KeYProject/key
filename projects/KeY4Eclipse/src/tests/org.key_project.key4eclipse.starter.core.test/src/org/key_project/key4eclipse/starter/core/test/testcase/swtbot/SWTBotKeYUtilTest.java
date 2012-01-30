package org.key_project.key4eclipse.starter.core.test.testcase.swtbot;

import java.io.File;
import java.lang.reflect.InvocationTargetException;

import junit.framework.TestCase;

import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jdt.core.IClasspathEntry;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.jdt.core.JavaCore;
import org.eclipse.jdt.core.Signature;
import org.junit.Test;
import org.key_project.key4eclipse.starter.core.test.Activator;
import org.key_project.key4eclipse.starter.core.util.KeYUtil;
import org.key_project.key4eclipse.util.eclipse.BundleUtil;
import org.key_project.key4eclipse.util.eclipse.ResourceUtil;
import org.key_project.key4eclipse.util.java.SwingUtil;
import org.key_project.key4eclipse.util.jdt.JDTUtil;
import org.key_project.key4eclipse.util.test.util.TestUtilsUtil;
import org.key_project.swtbot.swing.bot.SwingBot;
import org.key_project.swtbot.swing.bot.SwingBotJDialog;
import org.key_project.swtbot.swing.bot.SwingBotJLabel;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.proof.init.InitConfig;

/**
 * SWT Bot tests for {@link KeYUtil}.
 * @author Martin Hentschel
 */
public class SWTBotKeYUtilTest extends TestCase {
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
        SwingBotJLabel label = dialog.bot().jLabel(exception.toString()); // On Mac OS it is not the first label.
        assertEquals(exception.toString(), label.getText());
        dialog.close();
    }

    /**
     * Tests {@link KeYUtil#startProof(org.eclipse.jdt.core.IMethod)} and
     * {@link KeYUtil#startProofAsync(org.eclipse.jdt.core.IMethod)}.
     */
    @Test
    public void testStartProof() throws Exception {
        // Load java project with multiple source directories
        final IJavaProject javaProject = TestUtilsUtil.createJavaProject("SWTBotKeYUtilTest_testStartProof_Java");
        IFolder banking = javaProject.getProject().getFolder("src").getFolder("banking");
        if (!banking.exists()) {
            banking.create(true, true, null);
        }
        BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/banking", banking);
        IFolder secondSrc = javaProject.getProject().getFolder("secondSrc");
        if (!secondSrc.exists()) {
            secondSrc.create(true, true, null);
        }
        IClasspathEntry[] oldEntries = javaProject.getRawClasspath();
        JDTUtil.addClasspathEntry(javaProject, JavaCore.newSourceEntry(secondSrc.getFullPath()));
        IMethod chargeMehtod = TestUtilsUtil.getJdtMethod(javaProject, "banking.PayCard", "charge", Signature.C_INT + "");
        try {
            KeYUtil.startProof(chargeMehtod);
            fail("Multiple source paths are not supported.");
        }
        catch (Exception e) {
            assertTrue(e.getMessage(), e.getMessage().contains("Multiple source paths are not supported."));
        }
        javaProject.setRawClasspath(oldEntries, null);
        // Load java project with one source directory
        KeYUtil.startProofAsync(chargeMehtod);
        TestUtilsUtil.keyStartSelectedProofInProofManagementDiaolog();
        TestUtilsUtil.keyCheckProofs("JML operation contract [id: 1 / banking.PayCard::charge]", "JML operation contract [id: 1 / banking.PayCard::charge]");
        // Load second java project
        IJavaProject secondProject = TestUtilsUtil.createJavaProject("SWTBotKeYUtilTest_testStartProof_Java2");
        BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/MCDemo", secondProject.getProject().getFolder("src"));
        IMethod incMethod = TestUtilsUtil.getJdtMethod(secondProject, "MCDemo", "inc", Signature.C_INT + "");
        KeYUtil.startProofAsync(incMethod);
        TestUtilsUtil.keyStartSelectedProofInProofManagementDiaolog();
        TestUtilsUtil.keyCheckProofs("JML normal_behavior operation contract [id: 0 / MCDemo::inc]", "JML operation contract [id: 1 / banking.PayCard::charge]", "JML normal_behavior operation contract [id: 0 / MCDemo::inc]");
        // Open first project again to make sure that only the proof is selected again and no second proof environment is created
        KeYUtil.startProofAsync(chargeMehtod);
        TestUtilsUtil.keyGoToSelectedProofInProofManagementDiaolog();
        TestUtilsUtil.keyCheckProofs("JML operation contract [id: 1 / banking.PayCard::charge]", "JML operation contract [id: 1 / banking.PayCard::charge]", "JML normal_behavior operation contract [id: 0 / MCDemo::inc]");
        // Clear proof list
        KeYUtil.clearProofList(MainWindow.getInstance());
        TestCase.assertTrue(KeYUtil.isProofListEmpty(MainWindow.getInstance()));
        // Close main window
        TestUtilsUtil.keyCloseMainWindow();
    }
    
    /**
     * Tests {@link KeYUtil#getInitConfig(java.io.File)}
     */
    @Test
    public void testGetInitConfig() throws CoreException, InterruptedException, InvocationTargetException {
        // Open main window
        KeYUtil.openMainWindow();
        assertNotNull(MainWindow.getInstance());
        assertTrue(KeYUtil.isProofListEmpty(MainWindow.getInstance()));
        // Load a resource
        IJavaProject javaProject = TestUtilsUtil.createJavaProject("SWTBotKeYUtilTest_testGetInitConfig_1");
        BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/banking", javaProject.getProject().getFolder("src"));
        KeYUtil.loadAsync(javaProject.getProject());
        TestUtilsUtil.keyStartSelectedProofInProofManagementDiaolog();
        TestUtilsUtil.keyCheckProofs("JML operation contract [id: 0 / banking.LoggingPayCard::charge]", "JML operation contract [id: 0 / banking.LoggingPayCard::charge]");
        assertNotNull(MainWindow.getInstance());
        assertFalse(KeYUtil.isProofListEmpty(MainWindow.getInstance()));
        // Load second java project
        IJavaProject secondProject = TestUtilsUtil.createJavaProject("SWTBotKeYUtilTest_testGetInitConfig_2");
        BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/MCDemo", secondProject.getProject().getFolder("src"));
        KeYUtil.loadAsync(secondProject.getProject());
        TestUtilsUtil.keyStartSelectedProofInProofManagementDiaolog();
        TestUtilsUtil.keyCheckProofs("JML normal_behavior operation contract [id: 0 / MCDemo::inc]", "JML operation contract [id: 0 / banking.LoggingPayCard::charge]", "JML normal_behavior operation contract [id: 0 / MCDemo::inc]");
        assertNotNull(MainWindow.getInstance());
        assertFalse(KeYUtil.isProofListEmpty(MainWindow.getInstance()));
        // Check first environment
        File firstLocation = ResourceUtil.getLocation(javaProject.getProject().getFolder("src"));
        InitConfig firstConfig = KeYUtil.getInitConfig(firstLocation);
        assertNotNull(firstConfig);
        assertEquals(firstConfig.getProofEnv().getJavaModel().getModelDir(), firstLocation.getAbsolutePath());
        // Check second environment
        File secondLocation = ResourceUtil.getLocation(secondProject.getProject().getFolder("src"));
        InitConfig secondConfig = KeYUtil.getInitConfig(secondLocation);
        assertNotNull(secondConfig);
        assertEquals(secondConfig.getProofEnv().getJavaModel().getModelDir(), secondLocation.getAbsolutePath());
        // Test invalid location
        File invalidLocation = ResourceUtil.getLocation(secondProject.getProject());
        assertNull(KeYUtil.getInitConfig(invalidLocation));
        // Test null
        assertNull(KeYUtil.getInitConfig(null));
        // Remove first proof again
        KeYUtil.clearProofList(MainWindow.getInstance());
        TestCase.assertTrue(KeYUtil.isProofListEmpty(MainWindow.getInstance()));
        // Close main window
        TestUtilsUtil.keyCloseMainWindow();
    }

    /**
     * Tests {@link KeYUtil#removeFromProofList(MainWindow, de.uka.ilkd.key.proof.mgt.ProofEnvironment)}
     */
    @Test
    public void testRemoveFromProofList() throws CoreException, InterruptedException, InvocationTargetException {
        // Open main window
        KeYUtil.openMainWindow();
        assertNotNull(MainWindow.getInstance());
        assertTrue(KeYUtil.isProofListEmpty(MainWindow.getInstance()));
        // Load a resource
        IJavaProject javaProject = TestUtilsUtil.createJavaProject("SWTBotKeYUtilTest_testRemoveFromProofList_1");
        BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/banking", javaProject.getProject().getFolder("src"));
        KeYUtil.loadAsync(javaProject.getProject());
        TestUtilsUtil.keyStartSelectedProofInProofManagementDiaolog();
        TestUtilsUtil.keyCheckProofs("JML operation contract [id: 0 / banking.LoggingPayCard::charge]", "JML operation contract [id: 0 / banking.LoggingPayCard::charge]");
        assertNotNull(MainWindow.getInstance());
        assertFalse(KeYUtil.isProofListEmpty(MainWindow.getInstance()));
        // Load second java project
        IJavaProject secondProject = TestUtilsUtil.createJavaProject("SWTBotKeYUtilTest_testRemoveFromProofList_2");
        BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/MCDemo", secondProject.getProject().getFolder("src"));
        KeYUtil.loadAsync(secondProject.getProject());
        TestUtilsUtil.keyStartSelectedProofInProofManagementDiaolog();
        TestUtilsUtil.keyCheckProofs("JML normal_behavior operation contract [id: 0 / MCDemo::inc]", "JML operation contract [id: 0 / banking.LoggingPayCard::charge]", "JML normal_behavior operation contract [id: 0 / MCDemo::inc]");
        assertNotNull(MainWindow.getInstance());
        assertFalse(KeYUtil.isProofListEmpty(MainWindow.getInstance()));
        // Remove first proof
        KeYUtil.removeFromProofList(MainWindow.getInstance(), TestUtilsUtil.keyGetProofEnv(0));
        TestCase.assertFalse(KeYUtil.isProofListEmpty(MainWindow.getInstance()));
        TestUtilsUtil.keyCheckProofs("JML normal_behavior operation contract [id: 0 / MCDemo::inc]", "JML normal_behavior operation contract [id: 0 / MCDemo::inc]");
        // Remove first proof again
        KeYUtil.removeFromProofList(MainWindow.getInstance(), TestUtilsUtil.keyGetProofEnv(0));
        TestCase.assertTrue(KeYUtil.isProofListEmpty(MainWindow.getInstance()));
        // Close main window
        TestUtilsUtil.keyCloseMainWindow();
    }
    
    /**
     * Tests {@link KeYUtil#clearProofList(MainWindow)}
     */
    @Test
    public void testClearProofList() throws CoreException, InterruptedException, InvocationTargetException {
        // Open main window
        KeYUtil.openMainWindow();
        assertNotNull(MainWindow.getInstance());
        assertTrue(KeYUtil.isProofListEmpty(MainWindow.getInstance()));
        // Load a resource
        IJavaProject javaProject = TestUtilsUtil.createJavaProject("SWTBotKeYUtilTest_testClearProofList_1");
        BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/banking", javaProject.getProject().getFolder("src"));
        KeYUtil.loadAsync(javaProject.getProject());
        TestUtilsUtil.keyStartSelectedProofInProofManagementDiaolog();
        TestUtilsUtil.keyCheckProofs("JML operation contract [id: 0 / banking.LoggingPayCard::charge]", "JML operation contract [id: 0 / banking.LoggingPayCard::charge]");
        assertNotNull(MainWindow.getInstance());
        assertFalse(KeYUtil.isProofListEmpty(MainWindow.getInstance()));
        // Load second java project
        IJavaProject secondProject = TestUtilsUtil.createJavaProject("SWTBotKeYUtilTest_testClearProofList_2");
        BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/MCDemo", secondProject.getProject().getFolder("src"));
        KeYUtil.loadAsync(secondProject.getProject());
        TestUtilsUtil.keyStartSelectedProofInProofManagementDiaolog();
        TestUtilsUtil.keyCheckProofs("JML normal_behavior operation contract [id: 0 / MCDemo::inc]", "JML operation contract [id: 0 / banking.LoggingPayCard::charge]", "JML normal_behavior operation contract [id: 0 / MCDemo::inc]");
        assertNotNull(MainWindow.getInstance());
        assertFalse(KeYUtil.isProofListEmpty(MainWindow.getInstance()));
        // Remove proof
        KeYUtil.clearProofList(MainWindow.getInstance());
        TestCase.assertTrue(KeYUtil.isProofListEmpty(MainWindow.getInstance()));
        // Close main window
        TestUtilsUtil.keyCloseMainWindow();
    }
    
    /**
     * Tests {@link KeYUtil#isProofListEmpty(MainWindow)}
     */
    @Test
    public void testIsProofListEmpty() throws CoreException, InterruptedException, InvocationTargetException {
        // Open main window
        KeYUtil.openMainWindow();
        assertNotNull(MainWindow.getInstance());
        assertTrue(KeYUtil.isProofListEmpty(MainWindow.getInstance()));
        // Load a resource
        IJavaProject javaProject = TestUtilsUtil.createJavaProject("SWTBotKeYUtilTest_testIsProofListEmpty");
        BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/banking", javaProject.getProject().getFolder("src"));
        KeYUtil.loadAsync(javaProject.getProject());
        TestUtilsUtil.keyStartSelectedProofInProofManagementDiaolog();
        TestUtilsUtil.keyCheckProofs("JML operation contract [id: 0 / banking.LoggingPayCard::charge]", "JML operation contract [id: 0 / banking.LoggingPayCard::charge]");
        assertNotNull(MainWindow.getInstance());
        assertFalse(KeYUtil.isProofListEmpty(MainWindow.getInstance()));
        // Remove proof
        KeYUtil.clearProofList(MainWindow.getInstance());
        TestCase.assertTrue(KeYUtil.isProofListEmpty(MainWindow.getInstance()));
        // Close main window
        TestUtilsUtil.keyCloseMainWindow();
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
        JDTUtil.addClasspathEntry(javaProject, JavaCore.newSourceEntry(secondSrc.getFullPath()));
        try {
            KeYUtil.load(javaProject.getProject());
            fail("Multiple source paths are not supported.");
        }
        catch (Exception e) {
            assertTrue(e.getMessage(), e.getMessage().contains("Multiple source paths are not supported."));
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
