package org.key_project.key4eclipse.testcase;

import junit.framework.TestCase;

import org.junit.Test;

import de.uka.ilkd.key.gui.Main;
import de.uka.ilkd.key.gui.MainWindow;

/**
 * Tests for {@link Main}.
 * @author Martin Hentschel
 */
public class MainTest extends TestCase {
    /**
     * Starts the normal KeY application via {@link Main#main(String[])}
     * and closes it. If something is wrong with the KeY eclipse integration
     * an exception is thrown. 
     */
    @Test
    public void testOpeningMainWindow() {
        // Open KeY user interface and make sure that a window is opened.
        Main.main(new String[] {});
        assertNotNull(MainWindow.getInstance());
        assertTrue(MainWindow.getInstance().isVisible());
        // Get main window and close it
        MainWindow.getInstance().setVisible(false);
        assertFalse(MainWindow.getInstance().isVisible());
    }
}
