package de.uka.ilkd.key.nui.tests.guitests;

import static org.junit.Assert.assertEquals;

import org.junit.Test;

import de.uka.ilkd.key.nui.exceptions.ComponentNotFoundException;
import de.uka.ilkd.key.nui.prooftree.NUINode;
import javafx.application.Platform;
import javafx.scene.Node;
import javafx.scene.control.Slider;

/**
 * Test for User Story: Strategy-View Komponente (#15077)
 * 
 * @author Patrick Jattke
 *
 */

@SuppressWarnings("PMD.AtLeastOneConstructor")
// PMD will also complain if adding the constructor, then saying "avoid useless
// constructors"
public class StrategyViewTest extends NUITestHelper {

    /**
     * Checks whether the 'GO' button in the slider works properly.
     */
    @Test
    public void executeGoButtonDefault() {
        loadProof("example01.key", false);
        assertEquals(2, countLoadedNodes());
        clickOn("#goButton");
        waitUntilStatusIs(
                "Maximal number of rule applications reached or timed out.");

        assertEquals(12, countLoadedNodes());
    }

    /**
     * Moves the slider for the maximum rule applications, executes the goButton
     * and checks whether the proof was modified.
     */
    @Test
    public void setSliderExecuteGoButton() {
        loadProof("example01.key", false);
        assertEquals(2, countLoadedNodes());

        try {
            for (Node n : nui.getComponent("strategyViewPane").getChildren()) {
                if (n.getId() != null
                        && n.getId().contains("maxRuleAppSlider")) {
                    Platform.runLater(() -> ((Slider) n).setValue(1.7));
                    break;
                }
            }
        }
        catch (ComponentNotFoundException e) {
            e.printStackTrace();
        }

        clickOn("#goButton");
        waitUntilStatusIs(
                "No more rules automatically applicable to any goal.");

        assertEquals(49, countLoadedNodes());
    }

    /**
     * Counts the {@link NUINode NUINodes} of the currently loaded tree.
     * 
     * @return an int indicating the number of nodes in the tree.
     */
    private int countLoadedNodes() {
        return (int) nui.getDataModel().getLoaddTriVwStat().getTreeItem()
                .getValue().asList().stream().count();
    }

}
