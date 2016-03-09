package de.uka.ilkd.key.nui.tests.guitests;

import static org.junit.Assert.assertTrue;

import org.junit.Before;
import org.junit.Test;

/**
 * Tests for User Story (001) Oberflaeche: Grundaufbau #14297
 * 
 * GUI test for main application window
 *
 * @author Florian Breitfelder
 * @author Patrick Jattke
 *
 */
public class MoveViewTest extends NUITest {

    // IDs of the panes where the views can be placed on
    private final String DIRECTION_BOTTOM = "bottom";
    private final String DIRECTION_RIGHT = "right";
    private final String DIRECTION_LEFT = "left";
    private final String DIRECTION_MIDDLE = "middle";

    // Text of the items in the menu bar
    private static final String MENUBAR_ABOUT = "About";
    private static final String MENUBAR_VIEW = "View";
    private static final String MENUBAR_EDIT = "Edit";
    private static final String MENUBAR_FILE = "File";

    // IDs of the views
    private static final String CONFIG_VIEWS = "#configViews";

    private String hide = null;
    private String left = null;
    private String middle = null;
    private String right = null;
    private String bottom = null;

    @Before
    public void setupTest() throws Throwable {
        // mapViewsToToggleGroups();
        hide = nui.getText("hide");
        left = nui.getText("left");
        middle = nui.getText("middle");
        right = nui.getText("right");
        bottom = nui.getText("bottom");
    }

    @Test
    public void testFileMenu() {
        // FILE
        // Testing 'Close' is not possible (see
        // https://github.com/TestFX/TestFX/issues/50)

        // FILE
        // Test open file dialog
        clickOn(MENUBAR_FILE).clickOn("Open Proof...");
        // close open file dialog directly
        // Load file tests in LoadProofTest
        this.closeCurrentWindow();

        // EDIT
        clickOn(MENUBAR_EDIT);

        // VIEW
        // configViews is tested by testToogleGroupX
        clickOn(MENUBAR_VIEW);

        // ABOUT
        clickOn(MENUBAR_ABOUT).clickOn("About KeY");
        // close ABOUT window
        this.closeCurrentWindow();
        clickOn(MENUBAR_ABOUT).clickOn("License");
    }

    @Test
    public void testMoveOpenProofsView() {
        /*
         * componendId must starts with # hence testfx interprets componedId as
         * JavaFX fxid
         */
        String componendId = "#openProofsViewPane";
        String subMenuName = nui.getText("openProofsViewPane");

        loadProof("example01.proof");
        moveViewTester(componendId, subMenuName);
    }

    @Test
    public void testMoveTreeView() {
        /*
         * componendId must starts with # hence testfx interprets componedId as
         * JavaFX fxid
         */
        String componendId = "#treeViewPane";
        String subMenuName = nui.getText("treeViewPane");
        
        loadProof("example01.proof");
        moveViewTester(componendId, subMenuName);
    }

    @Test
    public void testMoveStrategyView() {
        /*
         * componendId must starts with # hence testfx interprets componedId as
         * JavaFX fxid
         */
        String componendId = "#strategyViewPane";
        String subMenuName = nui.getText("strategyViewPane");
        
        loadProof("example01.proof");
        moveViewTester(componendId, subMenuName);
    }

    @Test
    public void testMoveProofView() {
        /*
         * componendId must starts with # hence testfx interprets componedId as
         * JavaFX fxid
         */
        String componendId = "#proofViewPane";
        String subMenuName = nui.getText("proofViewPane");
        
        loadProof("example01.proof");
        moveViewTester(componendId, subMenuName);
    }

    /**
     * This method tests if it is possible to move view.
     * 
     * @param hide
     *            text to identify position of the hide submenu
     * @param left
     *            text to identify position of the left submenu
     * @param middle
     *            text to identify position of the middle submenu
     * @param right
     *            text to identify position of the right submenu
     * @param bottom
     *            text to identify position of the bottom submenu
     */
    private void moveViewTester(final String componendId,
            final String subMenuName) {
        // String subMenuName = (String) viewMap.get(componendId);

        // place view on HIDE
        clickOn(MENUBAR_VIEW).moveTo(CONFIG_VIEWS).moveTo(subMenuName)
                .moveTo(hide).clickOn(hide);
        assertTrue(!find(componendId).isVisible());

        // place view on LEFT pane
        clickOn(MENUBAR_VIEW).moveTo(CONFIG_VIEWS).moveTo(subMenuName)
                .moveTo(hide).clickOn(left);
        assertTrue(find(componendId).isVisible());
        assertTrue(
                find(componendId).getParent().getId().equals(DIRECTION_LEFT));
        assertTrue(find(componendId).isResizable());

        // place view on MIDDLE pane
        clickOn(MENUBAR_VIEW).moveTo(CONFIG_VIEWS).moveTo(subMenuName)
                .moveTo(hide).clickOn(middle);
        assertTrue(find(componendId).isVisible());
        assertTrue(
                find(componendId).getParent().getId().equals(DIRECTION_MIDDLE));

        // place view on RIGHT pane
        clickOn(MENUBAR_VIEW).moveTo(CONFIG_VIEWS).moveTo(subMenuName)
                .moveTo(hide).clickOn(right);
        assertTrue(find(componendId).isVisible());
        assertTrue(
                find(componendId).getParent().getId().equals(DIRECTION_RIGHT));

        // place view on BOTTOM pane
        clickOn(MENUBAR_VIEW).moveTo(CONFIG_VIEWS).moveTo(subMenuName)
                .moveTo(hide).clickOn(bottom);
        assertTrue(find(componendId).isVisible());
        assertTrue(
                find(componendId).getParent().getId().equals(DIRECTION_BOTTOM));

        // place view on HIDE pane
        clickOn(MENUBAR_VIEW).moveTo(CONFIG_VIEWS).moveTo(subMenuName)
                .moveTo(hide).clickOn(hide);
        assertTrue(!find(componendId).isVisible());
    }
}