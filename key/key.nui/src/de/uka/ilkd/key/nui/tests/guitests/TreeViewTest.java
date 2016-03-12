package de.uka.ilkd.key.nui.tests.guitests;

import org.junit.Test;

import de.uka.ilkd.key.nui.prooftree.ProofTreeStyleConstants;
import javafx.scene.input.KeyCode;

/**
 * Test for User Stroys
 * (002) Beweisbaumvisualisierung #14298
 * (007) Farbige Hinterlegung von Knoten im Beweisbaum #14662
 * (008) Icons im Beweisbaum #14470
 * (009) Basis Kontextmenu mit "Expand/Collapse all" #14663
 * 
 * Basic tests for treeView Component
 * 
 * @author Florian Breitfelder
 *
 */
public class TreeViewTest extends NUITest {

    @Test
    public void testTreeNavigation() {
        // open load file dialog
        clickOn("File").clickOn("Open Proof...");
        
        // Enter file name: example01.proof
        KeyCodeHelper key = new KeyCodeHelper(this);
        key.typeKeys(key.getKeyCode("EXAMPLE01.PROOF"));
 
        // press enter to load file
        type(KeyCode.ENTER);
        
    	doubleClickOn("." + ProofTreeStyleConstants.CSS_NODE_BRANCH);
    	clickOn("0: andRight ");
    	doubleClickOn("Case 1 ");
    	doubleClickOn("Case 2 ");
    	doubleClickOn("Case 1 ");
    	rightClickOn().clickOn("Expand All");
    	clickOn("Case 1");
    	rightClickOn().clickOn("Expand All");
    	clickOn("Case 1");
    	rightClickOn().clickOn("Expand All");
    	clickOn("Case 1");
    	rightClickOn().clickOn("Expand All");
    	clickOn("Case 1");
    	rightClickOn().clickOn("Expand All");
    	clickOn("Case 1");
    	//rightClickOn().clickOn("Expand Below");
    	//rightClickOn().clickOn("Collapse All");
    	//rightClickOn().clickOn("Collapse Below");
    	/*rightClickOn().clickOn("Search");
    	rightClickOn().clickOn("Search");
    	rightClickOn().clickOn("Search");
    	rightClickOn().clickOn("Search");
    	rightClickOn().clickOn("Search");
    	rightClickOn().clickOn("Search");
    	rightClickOn().clickOn("Search");
    	rightClickOn().clickOn("Search");
    	rightClickOn().clickOn("Search");
    	rightClickOn().clickOn("Search");
    	rightClickOn().clickOn("Search");
    	
    	write("Case 1");*/
    	// TODO test is not working. Find a way to address nodes in the tree.
       /* for (int i = 0; i < 15; i++) {
        	doubleClickOn("#Proof_Tree");
        }

        for (int i = 0; i < 25; i++) {
            scroll(VerticalDirection.DOWN);
        }

        doubleClickOn("#if_x_true");
        doubleClickOn("#if_x_false");*/
    }
}
