package org.key_project.key4eclipse.util.test.testcase.swtbot;

import junit.framework.TestCase;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jdt.core.IJavaProject;
import org.junit.Test;
import org.key_project.key4eclipse.util.eclipse.BundleUtil;
import org.key_project.key4eclipse.util.key.KeYUtil;
import org.key_project.key4eclipse.util.test.Activator;
import org.key_project.key4eclipse.util.test.util.TestUtilsUtil;
import org.key_project.swtbot.swing.bot.SwingBot;
import org.key_project.swtbot.swing.bot.SwingBotJButton;
import org.key_project.swtbot.swing.bot.SwingBotJDialog;
import org.key_project.swtbot.swing.bot.SwingBotJFrame;

import de.uka.ilkd.key.util.KeYResourceManager;

/**
 * SWT Bot tests for {@link KeYUtil}.
 * @author Martin Hentschel
 */
public class SWTBotKeYUtilTest extends TestCase {
    /**
     * Tests {@link KeYUtil#load(org.eclipse.core.resources.IResource)}.
     */
    @Test
    public void testLoad() throws CoreException, InterruptedException {
        // Try to load general project in KeY.
        IProject project = TestUtilsUtil.createProject("SWTBotKeYUtilTest_testLoad_general");
        try {
            KeYUtil.load(project);
            fail("Loading general projects should not be possible.");
        }
        catch (Exception e) {
            assertTrue(e.getMessage(), e.getMessage().contains("The project \"" + project + "\" is no Java project."));
        }
        // Load java project with one source directory
        IJavaProject javaProject = TestUtilsUtil.createJavaProject("SWTBotKeYUtilTest_testLoad_Java");
        BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/banking", javaProject.getProject().getFolder("src"));
        KeYUtil.load(javaProject.getProject());
        SwingBot bot = new SwingBot();
        SwingBotJFrame frame = bot.jFrame("KeY " + KeYResourceManager.getManager().getVersion());
        assertTrue(frame.isOpen());
        SwingBotJDialog dialog = frame.bot().jDialog("Proof Management");
        assertTrue(dialog.isOpen());
        SwingBotJButton startButton = dialog.bot().jButton("Start Proof");
        startButton.clickAndWait();
        assertFalse(dialog.isOpen());
        
//        frame.close();
//        assertFalse(frame.isOpen());
    }
    
    /**
     * Tests {@link KeYUtil#openMainWindow()}.
     */
    @Test
    public void testOpenMainWindow() {
        // Open main window
        KeYUtil.openMainWindow();
        // Close main window
        SwingBot bot = new SwingBot();
        SwingBotJFrame frame = bot.jFrame("KeY " + KeYResourceManager.getManager().getVersion());
        assertTrue(frame.isOpen());
        frame.close();
        assertFalse(frame.isOpen());
    }
}
