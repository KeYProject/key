package de.uka.ilkd.key.nui.tests.guitests;

import static org.junit.Assert.assertEquals;

import org.junit.Test;
import org.loadui.testfx.GuiTest;

public class SaveFunctionTest extends NUITestHelper {

    @Test
    public void testSaveDialogOnChange() {
        // FILE
        // Testing 'Close' is not possible (see
        // https://github.com/TestFX/TestFX/issues/50)

        // test load proof
        loadProof("example01.key", false);

        // apply strategy (change proof)
        clickOn("Start");

        // check if only the MainView window is open
        assertEquals(1, GuiTest.getWindows().size());

        // close program
        clickOn("File").clickOn("Close");

        // check if save dialog is open
        assertEquals(2, GuiTest.getWindows().size());
    }
}
