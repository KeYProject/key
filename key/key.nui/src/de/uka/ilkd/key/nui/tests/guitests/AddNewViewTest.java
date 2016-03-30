package de.uka.ilkd.key.nui.tests.guitests;

import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertTrue;

import java.io.File;
import java.io.IOException;
import java.nio.file.Files;

import org.junit.AfterClass;
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Test;

import de.uka.ilkd.key.nui.controller.MainViewController.Place;
import de.uka.ilkd.key.nui.exceptions.ComponentNotFoundException;

public class AddNewViewTest extends NUITest {
    // IDs of the panes where the views can be placed on
    private static final String DIRECTION_BOTTOM = "bottom";
    private static final String DIRECTION_RIGHT = "right";
    private static final String DIRECTION_LEFT = "left";
    private static final String DIRECTION_MIDDLE = "middle";

    private String hide = null;
    private String left = null;
    private String middle = null;
    private String right = null;
    private String bottom = null;

    // Text of the items in the menu bar
    private static final String MENUBAR_VIEW = "View";
    // IDs of the views
    private static final String CONFIG_VIEWS = "#configViews";

    private static File controllerS = new File(
            "bin//de/uka//ilkd//key//nui//tests//guitests//GUITestController.class");
    private static File controllerD = new File(
            "bin//de/uka//ilkd//key//nui//controller//GUITestController.class");

    private static File fxmlS = new File(
            "bin//de/uka//ilkd//key//nui//tests//guitests//GUITestView.fxml");
    private static File fxmlD = new File(
            "bin//de//uka//ilkd//key//nui//components//GUITestView.fxml");

    @BeforeClass
    public static void initTest() throws IOException {
        com.google.common.io.Files.copy(controllerS, controllerD);
        com.google.common.io.Files.copy(fxmlS, fxmlD);
    }

    /**
     * @throws Throwable
     */
    @Before
    public void setupTest() throws Throwable {
        hide = nui.getText("hide");
        left = nui.getText("left");
        middle = nui.getText("middle");
        right = nui.getText("right");
        bottom = nui.getText("bottom");
    }

    @AfterClass
    public static void finishing() throws IOException {
        Files.delete(controllerD.toPath());
        Files.delete(fxmlD.toPath());
    }

    @Test
    public void testAddingNewComponent() throws ComponentNotFoundException {
        nui.getMainViewCont().addComponent(nui.getComponent("GUITestViewPane"),
                Place.HIDDEN);
        /*
         * componendId must starts with # hence testfx interprets componedId as
         * JavaFX fxid
         */
        final String componendId = "#GUITestViewPane";
        final String subMenuName = nui.getText("GUITestViewPane");

        moveViewTester(componendId, subMenuName);
    }

    /**
     * This method tests if it is possible to move view the GUITestView
     * 
     * @param componentId
     *            The fx:id of the component to be moved.
     * @param subMenuName
     *            The name of the sub menu to elevate the moving action.
     */
    private void moveViewTester(final String componentId,
            final String subMenuName) {
        // hide all components
        clickOn(MENUBAR_VIEW).moveTo(CONFIG_VIEWS).moveTo(subMenuName)
                .moveTo(hide).clickOn(hide);
        assertNull(find(componentId));

        clickOn(MENUBAR_VIEW).moveTo(CONFIG_VIEWS)
                .moveTo(nui.getBundle().getString("treeViewPane")).moveTo(hide)
                .clickOn(hide);
        assertNull(find("#treeViewPane"));

        clickOn(MENUBAR_VIEW).moveTo(CONFIG_VIEWS)
                .moveTo(nui.getBundle().getString("proofViewPane")).moveTo(hide)
                .clickOn(hide);
        assertNull(find("#proofViewPane"));

        clickOn(MENUBAR_VIEW).moveTo(CONFIG_VIEWS)
                .moveTo(nui.getBundle().getString("strategyViewPane"))
                .moveTo(hide).clickOn(hide);
        assertNull(find("#strategyViewPane"));

        clickOn(MENUBAR_VIEW).moveTo(CONFIG_VIEWS)
                .moveTo(nui.getBundle().getString("openProofsViewPane"))
                .moveTo(hide).clickOn(hide);
        assertNull(find("#openProofsViewPane"));

        // place view on LEFT pane
        clickOn(MENUBAR_VIEW).moveTo(CONFIG_VIEWS).moveTo(subMenuName)
                .moveTo(hide).clickOn(left);
        assertTrue(find(componentId).isVisible());
        assertTrue(
                find(componentId).getParent().getId().equals(DIRECTION_LEFT));
        assertTrue(find(componentId).isResizable());

        // place view on MIDDLE pane
        clickOn(MENUBAR_VIEW).moveTo(CONFIG_VIEWS).moveTo(subMenuName)
                .moveTo(hide).clickOn(middle);
        assertTrue(find(componentId).isVisible());
        assertTrue(
                find(componentId).getParent().getId().equals(DIRECTION_MIDDLE));

        // place view on RIGHT pane
        clickOn(MENUBAR_VIEW).moveTo(CONFIG_VIEWS).moveTo(subMenuName)
                .moveTo(hide).clickOn(right);
        assertTrue(find(componentId).isVisible());
        assertTrue(
                find(componentId).getParent().getId().equals(DIRECTION_RIGHT));

        // place view on BOTTOM pane
        clickOn(MENUBAR_VIEW).moveTo(CONFIG_VIEWS).moveTo(subMenuName)
                .moveTo(hide).clickOn(bottom);
        assertTrue(find(componentId).isVisible());
        assertTrue(
                find(componentId).getParent().getId().equals(DIRECTION_BOTTOM));

        // place view on HIDE pane
        clickOn(MENUBAR_VIEW).moveTo(CONFIG_VIEWS).moveTo(subMenuName)
                .moveTo(hide).clickOn(hide);
        assertNull(find(componentId));
    }
}
