package de.uka.ilkd.key.nui.tests.guitests;

import static org.junit.Assert.assertTrue;

import java.util.HashMap;

import org.junit.BeforeClass;
import org.junit.Test;
import org.loadui.testfx.GuiTest;

import de.uka.ilkd.key.nui.ComponentFactory;
import javafx.scene.Parent;

/**
 * Tests for User Story
 * (001) Oberflaeche: Grundaufbau #14297
 * 
 * GUI test for main application window
 *
 * @author Florian Breitfelder
 * @author Patrick Jattke
 *
 */
public class MoveViewTest extends GuiTest {

	// IDs of the panes where the views can be placed on
	private static final String DIRECTION_BOTTOM = "bottom";
	private static final String DIRECTION_RIGHT = "right";
	private static final String DIRECTION_LEFT = "left";

	// Text of the items in the menu bar
	private static final String MENUBAR_ABOUT = "About";
	private static final String MENUBAR_VIEW = "View";
	private static final String MENUBAR_EDIT = "Edit";
	private static final String MENUBAR_FILE = "File";

	// IDs of the views
	private static final String TREE_VIEW = "#treeView";
	private static final String PROOF_VIEW = "#proofView";
	private static final String CONFIG_VIEWS = "#configViews";
	private static final String OPEN_PROOFS_VIEW = "#openProofsView";
	private static final String GOAL_VIEW = "#goalView";

	// IDs of the toggle groups
	private static final String TREE_VIEW_TOGGLE = "#toggletreeView";
	private static final String PROOF_VIEW_TOGGLE = "#toggleproofView";
	private static final String OPEN_PROOFS_TOGGLE = "#toggleopenProofsView";
	private static final String GOAL_TOGGLE = "#togglegoalView";

	// the root of the scene graph
	private Parent root = null;

	// the map containing the mapping: view ID <-> toggle group ID
	private static HashMap<String, String> viewMap;

	@BeforeClass
	public static void setupStage() throws Throwable {
		mapViewsToToggleGroups();
	}

	@Override
	public Parent getRootNode() {
		ComponentFactory factory = ComponentFactory.getInstance();
		ComponentFactory.setResourceDirectory("components/");
		root = factory.createNUISceneGraph();
		return root;
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
		clickOn(MENUBAR_ABOUT).clickOn("License");
	}

	public static void mapViewsToToggleGroups() {
		viewMap = new HashMap<>();
		viewMap.put(GOAL_VIEW, GOAL_TOGGLE);
		viewMap.put(OPEN_PROOFS_VIEW, OPEN_PROOFS_TOGGLE);
		viewMap.put(PROOF_VIEW, PROOF_VIEW_TOGGLE);
		viewMap.put(TREE_VIEW, TREE_VIEW_TOGGLE);
	}

	@Test
	public void testToggleGroup0() {
		final String hideTGroup = "#hideTG0";
		final String leftTGroup = "#leftTG0";
		final String middleTGroup = "#middleTG0";
		final String rightTGroup = "#rightTG0";
		final String bottomTGroup = "#bottomTG0";

		toggleGroupTester(hideTGroup, leftTGroup, middleTGroup, rightTGroup, bottomTGroup, GOAL_VIEW);
	}

	@Test
	public void testToggleGroup1() {
		final String hideTGroup = "#hideTG1";
		final String leftTGroup = "#leftTG1";
		final String middleTGroup = "#middleTG1";
		final String rightTGroup = "#rightTG1";
		final String bottomTGroup = "#bottomTG1";

		toggleGroupTester(hideTGroup, leftTGroup, middleTGroup, rightTGroup, bottomTGroup, OPEN_PROOFS_VIEW);
	}

	@Test
	public void testToggleGroup2() {
		final String hideTGroup = "#hideTG2";
		final String leftTGroup = "#leftTG2";
		final String middleTGroup = "#middleTG2";
		final String rightTGroup = "#rightTG2";
		final String bottomTGroup = "#bottomTG2";

		toggleGroupTester(hideTGroup, leftTGroup, middleTGroup, rightTGroup, bottomTGroup, PROOF_VIEW);
	}

	@Test
	public void testToggleGroup3() {
		final String hideTGroup = "#hideTG3";
		final String leftTGroup = "#leftTG3";
		final String middleTGroup = "#middleTG3";
		final String rightTGroup = "#rightTG3";
		final String bottomTGroup = "#bottomTG3";

		toggleGroupTester(hideTGroup, leftTGroup, middleTGroup, rightTGroup, bottomTGroup, TREE_VIEW);
	}

	/**
	 * This method tests the toggle groups in the 'View' menu
	 * 
	 * @param hideTG
	 *            The ID of the toggle for hiding the view
	 * @param leftTG
	 *            The ID of the toggle for moving the view to the left
	 * @param middleTG
	 *            The ID of the toggle for moving the view to the middle
	 * @param rightTG
	 *            The ID of the toggle for moving the view to the right
	 * @param bottomTG
	 *            The ID of the toggle for moving the view to the bottom
	 */
	private void toggleGroupTester(final String hideTG, final String leftTG, final String middleTG,
			final String rightTG, final String bottomTG, final String view) {
		String targetViewID = (String) viewMap.get(view);

		// place view on HIDE
		clickOn(MENUBAR_VIEW).moveTo(CONFIG_VIEWS).moveTo(targetViewID).moveTo(hideTG).clickOn(hideTG);
		assertTrue(find(view) == null);

		// place view on LEFT pane
		clickOn(MENUBAR_VIEW).moveTo(CONFIG_VIEWS).moveTo(targetViewID).moveTo(hideTG).clickOn(leftTG);
		assertTrue(find(view).isVisible());
		assertTrue(find(view).getParent().getId().equals(DIRECTION_LEFT));
		assertTrue(find(view).isResizable());

		// place view on MIDDLE pane
		clickOn(MENUBAR_VIEW).moveTo(CONFIG_VIEWS).moveTo(targetViewID).moveTo(hideTG).clickOn(middleTG);
		assertTrue(find(view).isVisible());
		final String DIRECTION_MIDDLE = "middle";
		assertTrue(find(view).getParent().getId().equals(DIRECTION_MIDDLE));

		// place view on RIGHT pane
		clickOn(MENUBAR_VIEW).moveTo(CONFIG_VIEWS).moveTo(targetViewID).moveTo(hideTG).clickOn(rightTG);
		assertTrue(find(view).isVisible());
		assertTrue(find(view).getParent().getId().equals(DIRECTION_RIGHT));

		// place view on BOTTOM pane
		clickOn(MENUBAR_VIEW).moveTo(CONFIG_VIEWS).moveTo(targetViewID).moveTo(hideTG).clickOn(bottomTG);
		assertTrue(find(view).isVisible());
		assertTrue(find(view).getParent().getId().equals(DIRECTION_BOTTOM));

		// place view on HIDE pane
		clickOn(MENUBAR_VIEW).moveTo(CONFIG_VIEWS).moveTo(targetViewID).moveTo(hideTG).clickOn(hideTG);
		assertTrue(find(view) == null);
	}
}