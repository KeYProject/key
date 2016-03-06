package de.uka.ilkd.key.nui.tests.guitests;
import java.util.concurrent.TimeUnit;

import org.junit.Test;
import org.loadui.testfx.GuiTest;

import de.uka.ilkd.key.nui.NUI;
import de.uka.ilkd.key.nui.prooftree.ProofTreeStyle;
import javafx.scene.Parent;
import javafx.scene.control.Label;
import javafx.scene.input.KeyCode;

/**
 * Test for User Stroy (010) Laden von Beweisen #14664
 * 
 * @author Florian Breitfelder
 *
 */
public class LoadProofTest extends GuiTest {

    // the root of the scene graph
    //private Parent root = null;

    private NUI nui = null;
    
    @Override
    protected Parent getRootNode() {
        nui = new NUI();
        try {
            nui.initializeNUI();
        }
        catch (Exception e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }
        return nui.getRoot();
    }

    @Test
    public void example01Test() throws InterruptedException {
        // open load file dialog
        clickOn("File").clickOn("Open Proof...");

        // Enter file name: example01.proof
        KeyCodeHelper key = new KeyCodeHelper(this);
        key.typeKeys(key.getKeyCode("EXAMPLE01.PROOF"));

        // press enter to load file
        type(KeyCode.ENTER);
        
        Label label = ((Label) find("#statustext"));
        
        while(!label.getText().equals("Ready.")){
            sleep(2000);
        }
        
        // navigate through example01 proof tree
        doubleClickOn("." + ProofTreeStyle.CSS_NODE_BRANCH);/*
                .clickOn("0: andRight ").clickOn("Case 1 ").clickOn("Case 2 ")
                .doubleClickOn("Case 2 ").clickOn("2: equiv_right ")
                .rightClickOn().clickOn("Collapse All");*/
        sleep(2000);
    }

    @Test
    public void example02Test() {
        // open load file dialog
        clickOn("File").clickOn("Open Proof...");

        // Enter file name: example01.proof
        KeyCodeHelper key = new KeyCodeHelper(this);
        key.typeKeys(key.getKeyCode("EXAMPLE02.PROOF"));

        // press enter to load file
        type(KeyCode.ENTER);
        
        // navigate through example02 proof tree
        doubleClickOn("." + ProofTreeStyle.CSS_NODE_BRANCH).clickOn("0: {} ")
                .clickOn("a TRUE ").clickOn("a FALSE ").doubleClickOn("a TRUE ")
                .clickOn("1: OPEN GOAL ").doubleClickOn("a FALSE ")
                .clickOn("2: notRight ").clickOn("3: OPEN GOAL ").rightClickOn()
                .clickOn("Collapse All");
    }

}
