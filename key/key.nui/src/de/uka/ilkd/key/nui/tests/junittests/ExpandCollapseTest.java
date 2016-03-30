package de.uka.ilkd.key.nui.tests.junittests;

import java.io.File;

import org.junit.Assert;
import org.junit.Test;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.nui.prooftree.NUIBranchNode;
import de.uka.ilkd.key.nui.prooftree.NUINode;
import de.uka.ilkd.key.nui.prooftree.ProofTreeActions;
import de.uka.ilkd.key.nui.prooftree.ProofTreeConverter;
import de.uka.ilkd.key.nui.prooftree.ProofTreeItem;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import javafx.scene.control.TreeItem;

/**
 * Test for User Story: 'Expand/Collapse All' und 'Expand/Collapse Below' im
 * Beweisbaum.
 * 
 * @author Patrick Jattke
 *
 */
public class ExpandCollapseTest {

    /**
     * The proof file 1 used for this test.
     */
    private static final String TESTFILE_01 = "resources//de/uka//ilkd//key//examples//example01.proof";

    /**
     * The proof file 3 used for this test.
     */
    private static final String TESTFILE_03 = "resources//de/uka//ilkd//key//examples//gcd.twoJoins.proof";

    /**
     * The ProofTreeVisualizer used to load the test file.
     */
    private ProofTreeConverter ptVisualizer;

    /**
     * Prepares the test environment.
     */
    public ProofTreeItem setUp(String proofFileName) {
        final File proofFile = new File(proofFileName);
        KeYEnvironment<?> environment;
        try {
            environment = KeYEnvironment.load(JavaProfile.getDefaultInstance(),
                    proofFile, null, null, null, true);
        }
        catch (ProblemLoaderException e) {
            throw new IllegalStateException(
                    "Could not set up testing environment.", e);
        }
        ptVisualizer = new ProofTreeConverter(environment.getLoadedProof());
        return ptVisualizer.createFXProofTree();
    }

    /**
     * Checks whether the 'Expand All' functionality works correctly.
     */
    @Test
    public void expandAllTest() {
        TreeItem<NUINode> tree = setUp(TESTFILE_01);
        ProofTreeActions.expandAll(tree);
        checkPropertyExpandCollapseAll(tree, true);
    }

    /**
     * Checks whether the 'Collapse All' functionality works correctly.
     */
    @Test
    public void collapseAllTest() {
        TreeItem<NUINode> tree = setUp(TESTFILE_01);
        ProofTreeActions.collapseAll(tree);
        checkPropertyExpandCollapseAll(tree, false);
    }

    /**
     * Checks whether the subtree rooted by <code>tree</code> fulfills the
     * property <code>isExpanded=desiredValue</code> for every node in the tree.
     * 
     * @param tree
     *            the root of the subtree to be checked
     * 
     * @param desiredValue
     *            the value which isExpanded should have for each node
     */
    private void checkPropertyExpandCollapseAll(TreeItem<NUINode> tree,
            boolean desiredValue) {
        boolean condition = tree.isExpanded();
        Assert.assertEquals(condition, desiredValue);
        if (condition && tree.getValue() instanceof NUIBranchNode) {
            for (TreeItem<NUINode> child : tree.getChildren()) {
                Assert.assertEquals(child.isExpanded(), desiredValue);
                checkPropertyExpandCollapseAll(child, desiredValue);
            }
        }
    }

    /**
     * Checks the 'Collapse Below' functionality by the test file
     * {@link #TESTFILE_03}.
     */
    @Test
    public void collapseBelowTest_03() {
        TreeItem<NUINode> tree = setUp(TESTFILE_03);
        TreeItem<NUINode> targetNode = tree.getChildren().get(77).getChildren()
                .get(39);
        ProofTreeActions.collapseBelow(targetNode);
        checkPropertyExpandedCollapsedBelow(tree, targetNode, true, true);
    }

    /**
     * Checks the 'Collapse Below' functionality by the test file
     * {@link #TESTFILE_01}.
     */
    @Test
    public void collapseBelowTest_01() {
        TreeItem<NUINode> tree = setUp(TESTFILE_01);
        TreeItem<NUINode> targetNode = tree.getChildren().get(1).getChildren()
                .get(2).getChildren().get(2);
        ProofTreeActions.collapseBelow(targetNode);
        checkPropertyExpandedCollapsedBelow(tree, targetNode, true, true);
    }

    /**
     * Checks the 'Collapse Expand' functionality by the test file
     * {@link #TESTFILE_03}.
     */
    @Test
    public void collapseExpandTest_03() {
        TreeItem<NUINode> tree = setUp(TESTFILE_03);
        TreeItem<NUINode> targetNode = tree.getChildren().get(77).getChildren()
                .get(39);
        ProofTreeActions.expandBelow(targetNode);
        checkPropertyExpandedCollapsedBelow(tree, targetNode, false, false);
    }

    /**
     * Checks the 'Collapse Expand' functionality by the test file
     * {@link #TESTFILE_01}.
     */
    @Test
    public void collapseExpandTest_01() {
        TreeItem<NUINode> tree = setUp(TESTFILE_01);
        TreeItem<NUINode> targetNode = tree.getChildren().get(1).getChildren()
                .get(2).getChildren().get(2);
        ProofTreeActions.expandBelow(targetNode);
        checkPropertyExpandedCollapsedBelow(tree, targetNode, false, false);
    }

    /**
     * Checks whether all nodes in the subtree rooted by {@code tree} fulfill
     * isExpanded=desiredValue. When node {@code belowNode} is reached, then all
     * children of this node must fulfull isExpanded!=desiredValue.
     * 
     * @param tree
     *            the root node of the subtree to check
     * @param belowNode
     *            the node where the expand/collapse below was applied to
     * @param desiredValue
     *            the value of isExpanded before reaching the node belowNode
     * @param initialValue
     *            must be the same as {@link desiredValue} when calling this
     *            method
     */
    private void checkPropertyExpandedCollapsedBelow(TreeItem<NUINode> tree,
            TreeItem<NUINode> belowNode, boolean desiredValue,
            boolean initialValue) {
        boolean condition = tree.isExpanded();

        // check root node
        if (tree.getValue() instanceof NUIBranchNode
                && tree.getValue().getLabel().contains("Proof Tree")) {
            // root node is always expanded
            Assert.assertEquals(true, condition);
        }
        // check all children
        else {
            for (TreeItem<NUINode> child : tree.getChildren()) {
                if (child.getValue() instanceof NUIBranchNode) {

                    // we are already at the collapseBelowNode or we are already
                    // below the collapseBelowNode -> check all children of the
                    // nodes
                    if (child.equals(belowNode)
                            || desiredValue != initialValue) {
                        Assert.assertEquals(desiredValue, child.isExpanded());
                        checkPropertyExpandedCollapsedBelow(child,
                                belowNode, child.equals(belowNode)
                                        ? !desiredValue : desiredValue,
                                initialValue);
                    }
                    // we still have not reached the collapseBelowNode, check
                    // all children of the nodes
                    else {
                        Assert.assertEquals(!desiredValue, child.isExpanded());
                        checkPropertyExpandedCollapsedBelow(child, belowNode,
                                desiredValue, initialValue);
                    }
                }
            }
        }
    }
}