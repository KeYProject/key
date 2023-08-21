/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.util;

import java.util.LinkedList;
import java.util.List;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.AbstractProfile;
import de.uka.ilkd.key.proof.init.InitConfig;

import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * Tests for {@link NodePreorderIterator}.
 *
 * @author Martin Hentschel
 */
public class TestNodePreorderIterator {
    /**
     * Tests a tree of {@link Node}s with three levels after root.
     */
    @Test
    public void testNodesThreeLevel() {
        // Create tree to test
        Proof proof =
            new Proof("target", new InitConfig(new Services(AbstractProfile.getDefaultProfile())));
        Node root = appendRoot(proof);
        Node l1 = appendNode(proof, root);
        Node l11 = appendNode(proof, l1);
        appendNode(proof, l11);
        appendNode(proof, l1);
        Node l2 = appendNode(proof, root);
        appendNode(proof, l2);
        Node l22 = appendNode(proof, l2);
        appendNode(proof, l22);
        appendNode(proof, l22);
        appendNode(proof, l2);
        appendNode(proof, root);
        Node l4 = appendNode(proof, root);
        appendNode(proof, l4);
        // Test tree
        ExpectedNode[] level111 = createExpectedNodes(3);
        ExpectedNode[] level11 = createExpectedNodes(new int[] { 2, 4 }, level111, null);
        ExpectedNode[] level122 = createExpectedNodes(8, 9);
        ExpectedNode[] level12 = createExpectedNodes(new int[] { 6, 7, 10 }, null, level122, null);
        ExpectedNode[] level14 = createExpectedNodes(13);
        ExpectedNode[] level1 =
            createExpectedNodes(new int[] { 1, 5, 11, 12 }, level11, level12, null, level14);
        assertRoot(root, createExpectedNodes(new int[] { 0 }, level1));
    }

    /**
     * Tests a tree of {@link Node}s with two levels after root.
     */
    @Test
    public void testNodesTwoLevel() {
        // Create tree to test
        Proof proof =
            new Proof("target", new InitConfig(new Services(AbstractProfile.getDefaultProfile())));
        Node root = appendRoot(proof);
        Node l1 = appendNode(proof, root);
        appendNode(proof, l1);
        appendNode(proof, l1);
        Node l2 = appendNode(proof, root);
        appendNode(proof, l2);
        appendNode(proof, l2);
        appendNode(proof, l2);
        appendNode(proof, root);
        Node l4 = appendNode(proof, root);
        appendNode(proof, l4);
        // Test tree
        ExpectedNode[] level11 = createExpectedNodes(2, 3);
        ExpectedNode[] level12 = createExpectedNodes(5, 6, 7);
        ExpectedNode[] level14 = createExpectedNodes(10);
        ExpectedNode[] level1 =
            createExpectedNodes(new int[] { 1, 4, 8, 9 }, level11, level12, null, level14);
        assertRoot(root, createExpectedNodes(new int[] { 0 }, level1));
    }

    /**
     * Tests a tree of {@link Node}s with one level after root.
     */
    @Test
    public void testNodesOneLevel() {
        // Create tree to test
        Proof proof =
            new Proof("target", new InitConfig(new Services(AbstractProfile.getDefaultProfile())));
        Node root = appendRoot(proof);
        appendNode(proof, root);
        appendNode(proof, root);
        appendNode(proof, root);
        appendNode(proof, root);
        // Test tree
        ExpectedNode[] level1 = createExpectedNodes(1, 2, 3, 4);
        assertRoot(root, createExpectedNodes(new int[] { 0 }, level1));
    }

    /**
     * Tests only a root {@link Node}.
     */
    @Test
    public void testEmptyRoot() {
        // Create tree to test
        Proof proof =
            new Proof("target", new InitConfig(new Services(AbstractProfile.getDefaultProfile())));
        Node root = appendRoot(proof);
        // Test tree
        assertRoot(root, createExpectedNodes(0));
    }

    /**
     * Makes sure that a {@link NodePreorderIterator} which iterates over the given {@link Node}
     * returns nodes in preorder iteration over the expected trees.
     *
     * @param element The {@link Node} to iterate over.
     * @param expectedRoots The expected values.
     */
    protected void assertRoot(Node element, ExpectedNode[] expectedRoots) {
        NodePreorderIterator iter = new NodePreorderIterator(element);
        assertEquals(computeChildIndexOnParent(element), iter.getChildIndexOnParent());
        assertExpectedNodes(iter, expectedRoots, false, 0);
        assertEquals(-1, iter.getChildIndexOnParent());
        assertFalse(iter.hasNext());
    }

    /**
     * Makes sure that the nodes returned by the given {@link NodePreorderIterator} are equal to the
     * defined model.
     *
     * @param iter The {@link NodePreorderIterator} to test.
     * @param expectedRoots The expected model.
     * @param iterateOverSubtree Start new sub tree iteration at the current node?
     * @param expectedParentReturns The number of expected parent returns.
     */
    protected int assertExpectedNodes(NodePreorderIterator iter, ExpectedNode[] expectedRoots,
            boolean iterateOverSubtree, int expectedParentReturns) {
        if (expectedRoots != null) {
            Assertions.assertNotNull(iter);
            int previousChildrenDepth = 0;
            for (ExpectedNode node : expectedRoots) {
                Assertions.assertTrue(iter.hasNext());
                int childIndexOnParent = iter.getChildIndexOnParent();
                int returnedParents = iter.getReturnedParents();
                assertEquals(previousChildrenDepth, returnedParents);
                Node next = iter.next();
                assertEquals(computeChildIndexOnParent(next), childIndexOnParent);
                Assertions.assertNotNull(next);
                assertEquals(node.getExpectedSerialNr(), next.serialNr());
                if (iterateOverSubtree) {
                    assertRoot(next, new ExpectedNode[] { node });
                }
                previousChildrenDepth = assertExpectedNodes(iter, node.getExpectedChildren(), true,
                    expectedParentReturns + 1);
            }
            return 1 + previousChildrenDepth;
        } else {
            return 1;
        }
    }

    protected int computeChildIndexOnParent(Node node) {
        Node parent = node.parent();
        if (parent != null) {
            return parent.getChildNr(node);
        } else {
            return -1;
        }
    }

    /**
     * Forms the expected tree.
     *
     * @author Martin Hentschel
     */
    protected static class ExpectedNode {
        /**
         * The expected serialnr.
         */
        private final int expectedSerialNr;

        /**
         * The expected children.
         */
        private ExpectedNode[] expectedChildren;

        /**
         * Constructor.
         *
         * @param expectedSerialNr The expected serialnr.
         */
        public ExpectedNode(int expectedSerialNr) {
            this.expectedSerialNr = expectedSerialNr;
        }

        /**
         * Constructor.
         *
         * @param expectedSerialNr The expected serialnr.
         * @param expectedChildren The expected children.
         */
        public ExpectedNode(int expectedSerialNr, ExpectedNode[] expectedChildren) {
            this.expectedSerialNr = expectedSerialNr;
            this.expectedChildren = expectedChildren;
        }

        /**
         * Returns the expected serialnr.
         *
         * @return The expected serialnr.
         */
        public int getExpectedSerialNr() {
            return expectedSerialNr;
        }

        /**
         * Returns the expected children.
         *
         * @return The expected children.
         */
        public ExpectedNode[] getExpectedChildren() {
            return expectedChildren;
        }

        /**
         * {@inheritDoc}
         */
        @Override
        public String toString() {
            return expectedSerialNr + " with "
                + (expectedChildren != null ? expectedChildren.length : 0) + " children";
        }
    }

    /**
     * Creates new {@link ExpectedNode}s with the given serialnrs and children.
     *
     * @param serialNrs The given serialnrs.
     * @param children The given children.
     * @return The created {@link ExpectedNode}s.
     */
    protected ExpectedNode[] createExpectedNodes(int[] serialNrs, ExpectedNode[]... children) {
        assertEquals(serialNrs.length, children.length);
        List<ExpectedNode> result = new LinkedList<>();
        for (int i = 0; i < serialNrs.length; i++) {
            result.add(new ExpectedNode(serialNrs[i], children[i]));
        }
        return result.toArray(new ExpectedNode[0]);
    }

    /**
     * Creates new {@link ExpectedNode}s with the given serialNrs.
     *
     * @param serialNrs The given serialNrs.
     * @return The created {@link ExpectedNode}s.
     */
    protected ExpectedNode[] createExpectedNodes(int... serialNrs) {
        List<ExpectedNode> result = new LinkedList<>();
        for (int serialNr : serialNrs) {
            result.add(new ExpectedNode(serialNr));
        }
        return result.toArray(new ExpectedNode[0]);
    }

    /**
     * Appends a new node to the given parent {@link Node}.
     *
     * @param proof The {@link Proof} which forms the test model.
     * @param parent The parent {@link Node} to add to.
     * @return The new created child {@link Node}.
     */
    protected Node appendNode(Proof proof, Node parent) {
        Node newChild = new Node(proof);
        parent.add(newChild);
        return newChild;
    }

    /**
     * Sets a new root {@link Node} on the proof.
     *
     * @param proof The {@link Proof} to set root on.
     * @return The created root {@link Node}.
     */
    protected Node appendRoot(Proof proof) {
        Node root = new Node(proof);
        proof.setRoot(root);
        return root;
    }
}
