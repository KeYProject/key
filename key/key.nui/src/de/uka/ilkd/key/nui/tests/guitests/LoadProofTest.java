package de.uka.ilkd.key.nui.tests.guitests;

import org.junit.Test;
import org.loadui.testfx.GuiTest;

import de.uka.ilkd.key.nui.ComponentFactory;
import de.uka.ilkd.key.nui.prooftree.ProofTreeStyle;
import javafx.scene.Parent;
import javafx.scene.input.KeyCode;

/**
 * Test for User Stroy
 * (010) Laden von Beweisen #14664
 * 
 * @author Florian Breitfelder
 *
 */
public class LoadProofTest extends GuiTest {

    // the root of the scene graph
    private Parent root = null;

    @Override
    protected Parent getRootNode() {
        ComponentFactory factory = ComponentFactory.getInstance();
        ComponentFactory.setResourceDirectory("components/");
        root = factory.createNUISceneGraph();
        return root;
    }

    @Test
    public void example01Test() {
        // open load file dialog
        clickOn("File").clickOn("Open Proof...");

        // Enter file name: example01.proof
        KeyCodeHelper key = new KeyCodeHelper(this);
        key.typeKeys(key.getKeyCode("EXAMPLE01.PROOF"));

        // press enter to load file
        type(KeyCode.ENTER);
        
        doubleClickOn("." + ProofTreeStyle.CSS_NODE_BRANCH);
    }

    @Test
    public void example02Test() {
        // open load file dialog
        clickOn("File").clickOn("Open Proof...");

        // Enter file name: example01.proof
        KeyCodeHelper key = new KeyCodeHelper(this);
        key.typeKeys(key.getKeyCode("EXAMPLE01.PROOF"));

        // press enter to load file
        type(KeyCode.ENTER);
    }

}
