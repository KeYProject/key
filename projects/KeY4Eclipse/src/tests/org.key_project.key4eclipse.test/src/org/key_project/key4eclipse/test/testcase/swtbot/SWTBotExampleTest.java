package org.key_project.key4eclipse.test.testcase.swtbot;

import java.lang.reflect.InvocationTargetException;

import junit.framework.TestCase;

import org.junit.Test;
import org.key_project.key4eclipse.starter.core.util.KeYUtil;
import org.key_project.key4eclipse.util.test.util.TestUtilsUtil;
import org.key_project.key4eclipse.util.test.util.TestUtilsUtil.MethodTreatment;
import org.key_project.swtbot.swing.bot.SwingBotJButton;
import org.key_project.swtbot.swing.bot.SwingBotJDialog;
import org.key_project.swtbot.swing.bot.SwingBotJFrame;
import org.key_project.swtbot.swing.bot.SwingBotJList;
import org.key_project.swtbot.swing.bot.SwingBotJMenu;

import de.uka.ilkd.key.gui.MainWindow;

/**
 * Tests the example dialog in the Eclipse integration.
 * @author Martin Hentschel
 */
public class SWTBotExampleTest extends TestCase {
    /**
     * Opens the example wizard, selects an example and loads it.
     */
    @Test
    public void testExampleDialog() throws InterruptedException, InvocationTargetException {
        // Open KeY
        KeYUtil.openMainWindowAsync();
        // Get KeY window
        SwingBotJFrame frame = TestUtilsUtil.keyGetMainWindow();
        // Open example dialog.
        SwingBotJMenu fileMenu = frame.bot().jMenuBar().menu("File");
        fileMenu.item("Load Example...").click();
        SwingBotJDialog dialog = frame.bot().jDialog("Load Example");
        SwingBotJList list = dialog.bot().jList();
        // Select example
        list.select(5);
        // Close dialog and load example
        SwingBotJButton loadButton = dialog.bot().jButton("Load Example");
        loadButton.clickAndWait();
        // Start proof
        TestUtilsUtil.keyStartSelectedProofInProofManagementDiaolog();
        TestUtilsUtil.keyCheckProofs("JML operation contract [id: 7 / MyClass::MyClass]", "JML operation contract [id: 7 / MyClass::MyClass]");
        // Finish proof automatically
        TestUtilsUtil.keyFinishSelectedProofAutomatically(frame, MethodTreatment.EXPAND);
        // Clear proof list
        KeYUtil.clearProofList(MainWindow.getInstance());
        TestCase.assertTrue(KeYUtil.isProofListEmpty(MainWindow.getInstance()));
        // Close main window
        TestUtilsUtil.keyCloseMainWindow();
    }
}
