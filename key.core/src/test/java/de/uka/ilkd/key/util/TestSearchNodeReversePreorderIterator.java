/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.util;


import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.AbstractProfile;
import de.uka.ilkd.key.proof.init.InitConfig;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Tests for {@link SearchNodeReversePreorderIterator}.
 *
 * @author Martin Hentschel
 */
public class TestSearchNodeReversePreorderIterator {
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
        assertRoot(root);
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
        assertRoot(root);
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
        assertRoot(root);
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
        assertRoot(root);
    }

    /**
     * Starts at all {@link Node}s of the given proof tree a reverse order traversal.
     *
     * @param root The root of the proof tree.
     */
    protected void assertRoot(Node root) {
        NodePreorderIterator iter = new NodePreorderIterator(root);
        ImmutableList<Node> reverseList = ImmutableSLList.nil();
        while (iter.hasNext()) {
            Node next = iter.next();
            reverseList = reverseList.prepend(next);
            assertReversePreorder(next, reverseList);
        }
    }

    /**
     * Tests a reverse iteration starting at the given {@link Node}.
     *
     * @param start The {@link Node} to start iteration.
     * @param expectedReverseList The expected previous {@link Node}s.
     */
    protected void assertReversePreorder(Node start, ImmutableList<Node> expectedReverseList) {
        SearchNodeReversePreorderIterator reverseIter =
            new SearchNodeReversePreorderIterator(start);
        assertTrue(reverseIter.hasPrevious());
        while (reverseIter.hasPrevious()) {
            Node previous = reverseIter.previous();
            assertEquals(previous, expectedReverseList.head());
            expectedReverseList = expectedReverseList.take(1); // Remove head
        }
        assertTrue(expectedReverseList.isEmpty(),
            "Reverse still contains " + expectedReverseList.size() + " elements.");
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
