package de.uka.ilkd.key.nui.guitests;

import static org.junit.Assert.*;

import org.junit.Test;
import org.loadui.testfx.GuiTest;

import de.uka.ilkd.key.nui.ComponentFactory;
import javafx.scene.Parent;

//import static org.junit.Assert.assertNull;
//import static org.testfx.api.FxAssert.verifyThat;

/**
 * Tests for User Story 1
 * 
 * GUI-Test for main application window
 *
 * @author Florian Breitfelder
 *
 */
public class NUITest extends GuiTest {

    private Parent root = null;

    @Override
    public Parent getRootNode() {
        ComponentFactory.setInstance("components/");
        ComponentFactory factory = ComponentFactory.getInstance();
        root = factory.createNUISceneGraph();
        return root;
    }

    @Test
    public void testFileMenu() {
        clickOn("File");
        /*
         * clickOn("Close"); Test if application was closed isn't possible. -->
         * https://github.com/TestFX/TestFX/issues/50
         */
        clickOn("Edit");
        clickOn("View");
        /*
         * configViews is tested by testToogleGroupX
         */
        clickOn("About").clickOn("About KeY");
        clickOn("About").clickOn("License");
    }

    @Test
    public void testToggleGroup0() {
        clickOn("View").moveTo("#configViews").moveTo("#togglegoalView")
                .moveTo("#hideTG0").clickOn("#hideTG0");
        assertTrue(find("#goalView") == null);

        clickOn("View").moveTo("#configViews").moveTo("#togglegoalView")
                .moveTo("#hideTG0").clickOn("#leftTG0");
        assertTrue(find("#goalView").isVisible());
        assertTrue(find("#goalView").getParent().getId().equals("left"));
        assertTrue(find("#goalView").isResizable());

        clickOn("View").moveTo("#configViews").moveTo("#togglegoalView")
                .moveTo("#hideTG0").clickOn("#middleTG0");
        assertTrue(find("#goalView").isVisible());
        assertTrue(find("#goalView").getParent().getId().equals("middle"));

        clickOn("View").moveTo("#configViews").moveTo("#togglegoalView")
                .moveTo("#hideTG0").clickOn("#rightTG0");
        assertTrue(find("#goalView").isVisible());
        assertTrue(find("#goalView").getParent().getId().equals("right"));

        clickOn("View").moveTo("#configViews").moveTo("#togglegoalView")
                .moveTo("#hideTG0").clickOn("#bottomTG0");
        assertTrue(find("#goalView").isVisible());
        assertTrue(find("#goalView").getParent().getId().equals("bottom"));

        clickOn("View").moveTo("#configViews").moveTo("#togglegoalView")
                .moveTo("#hideTG0").clickOn("#hideTG0");
        assertTrue(find("#goalView") == null);
    }

    @Test
    public void testToggleGroup1() {
        clickOn("View").moveTo("#configViews").moveTo("#toggleopenProofsView")
                .moveTo("#hideTG1").clickOn("#hideTG1");
        assertTrue(find("#openProofsView") == null);

        clickOn("View").moveTo("#configViews").moveTo("#toggleopenProofsView")
                .moveTo("#hideTG1").clickOn("#leftTG1");
        assertTrue(find("#openProofsView").isVisible());
        assertTrue(find("#openProofsView").getParent().getId().equals("left"));

        clickOn("View").moveTo("#configViews").moveTo("#toggleopenProofsView")
                .moveTo("#hideTG1").clickOn("#middleTG1");
        assertTrue(find("#openProofsView").isVisible());
        assertTrue(
                find("#openProofsView").getParent().getId().equals("middle"));

        clickOn("View").moveTo("#configViews").moveTo("#toggleopenProofsView")
                .moveTo("#hideTG1").clickOn("#rightTG1");
        assertTrue(find("#openProofsView").isVisible());
        assertTrue(find("#openProofsView").getParent().getId().equals("right"));

        clickOn("View").moveTo("#configViews").moveTo("#toggleopenProofsView")
                .moveTo("#hideTG1").clickOn("#bottomTG1");
        assertTrue(find("#openProofsView").isVisible());
        assertTrue(
                find("#openProofsView").getParent().getId().equals("bottom"));

        clickOn("View").moveTo("#configViews").moveTo("#toggleopenProofsView")
                .moveTo("#hideTG1").clickOn("#hideTG1");
        assertTrue(find("#openProofsView") == null);
    }

    @Test
    public void testToggleGroup2() {
        clickOn("View").moveTo("#configViews").moveTo("#toggleproofView")
                .moveTo("#hideTG2").clickOn("#hideTG2");
        assertTrue(find("#proofView") == null);

        clickOn("View").moveTo("#configViews").moveTo("#toggleproofView")
                .moveTo("#hideTG2").clickOn("#leftTG2");
        assertTrue(find("#proofView").isVisible());
        assertTrue(find("#proofView").getParent().getId().equals("left"));

        clickOn("View").moveTo("#configViews").moveTo("#toggleproofView")
                .moveTo("#hideTG2").clickOn("#middleTG2");
        assertTrue(find("#proofView").isVisible());
        assertTrue(find("#proofView").getParent().getId().equals("middle"));

        clickOn("View").moveTo("#configViews").moveTo("#toggleproofView")
                .moveTo("#hideTG2").clickOn("#rightTG2");
        assertTrue(find("#proofView").isVisible());
        assertTrue(find("#proofView").getParent().getId().equals("right"));

        clickOn("View").moveTo("#configViews").moveTo("#toggleproofView")
                .moveTo("#hideTG2").clickOn("#bottomTG2");
        assertTrue(find("#proofView").isVisible());
        assertTrue(find("#proofView").getParent().getId().equals("bottom"));

        clickOn("View").moveTo("#configViews").moveTo("#toggleproofView")
                .moveTo("#hideTG2").clickOn("#hideTG2");
        assertTrue(find("#proofView") == null);
    }

    @Test
    public void testToggleGroup3() {
        clickOn("View").moveTo("#configViews").moveTo("#toggletreeView")
                .moveTo("#hideTG3").clickOn("#hideTG3");
        assertTrue(find("#treeView") == null);

        clickOn("View").moveTo("#configViews").moveTo("#toggletreeView")
                .moveTo("#hideTG3").clickOn("#leftTG3");
        assertTrue(find("#treeView").isVisible());
        assertTrue(find("#treeView").getParent().getId().equals("left"));

        clickOn("View").moveTo("#configViews").moveTo("#toggletreeView")
                .moveTo("#hideTG3").clickOn("#middleTG3");
        assertTrue(find("#treeView").isVisible());
        assertTrue(find("#treeView").getParent().getId().equals("middle"));

        clickOn("View").moveTo("#configViews").moveTo("#toggletreeView")
                .moveTo("#hideTG3").clickOn("#rightTG3");
        assertTrue(find("#treeView").isVisible());
        assertTrue(find("#treeView").getParent().getId().equals("right"));

        clickOn("View").moveTo("#configViews").moveTo("#toggletreeView")
                .moveTo("#hideTG3").clickOn("#bottomTG3");
        assertTrue(find("#treeView").isVisible());
        assertTrue(find("#treeView").getParent().getId().equals("bottom"));

        clickOn("View").moveTo("#configViews").moveTo("#toggletreeView")
                .moveTo("#hideTG3").clickOn("#hideTG3");
        assertTrue(find("#treeView") == null);
    }
}