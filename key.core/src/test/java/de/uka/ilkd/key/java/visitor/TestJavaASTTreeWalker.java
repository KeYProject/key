/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.visitor;

import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.declaration.LocalVariableDeclaration;
import de.uka.ilkd.key.java.expression.literal.IntLiteral;
import de.uka.ilkd.key.rule.TacletForTests;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Tests for {@link JavaASTTreeWalker}.
 *
 * @author Tobias Reinhold
 */
public class TestJavaASTTreeWalker {
    @Test
    public void walker() {
        final SourceElement se = TacletForTests
                .parsePrg("{int i; int j = 1; i = j; if (i == j) { i = 2; } else { j = 2; } }");
        JavaASTTreeWalker walker = new JavaASTTreeWalker(se);

        // The root node should be a StatementBlock
        assertEquals(StatementBlock.class, walker.root().getClass());
        StatementBlock root = (StatementBlock) walker.root();
        SourceElement currentNode = walker.currentNode();
        assertEquals(currentNode, root,
            "In the beginning, the current node should be the root node.");

        // For the following assertions, I drew the AST of the source element on paper and used that
        // to verify the correctness of the walker.

        // First child of the root is a LocalVariableDeclaration; should be the next visited
        SourceElement firstChild = walker.firstChild();
        assertEquals(LocalVariableDeclaration.class, firstChild.getClass(),
            "The first child of the root should be a LocalVariableDeclaration.");
        assertEquals(root.getChildAt(0), firstChild,
            "walker.firstChild() should return the first child of the current node.");

        // The parent of the first child should be the root
        currentNode = walker.parentNode();
        assertEquals(root, currentNode, "The parent of the first child should be the root.");
        assertEquals(currentNode, walker.currentNode(),
            "The worker should not just return the new node but also visit it. (0)");

        // The next node should be the first child again
        currentNode = walker.nextNode();
        assertEquals(firstChild, currentNode, "The next node should be the first child.");
        assertEquals(currentNode, walker.currentNode(),
            "The worker should not just return the new node but also visit it. (1)");

        // Going back, we should be at the root again
        currentNode = walker.previousNode();
        assertEquals(root, currentNode, "The previous node should be the root again.");
        assertEquals(currentNode, walker.currentNode(),
            "The worker should not just return the new node but also visit it. (2)");

        // The last child (the fourth) of the root should be an If
        currentNode = walker.lastChild();
        assertEquals(root.getChildAt(3), currentNode,
            "walker.lastChild() should here return the last (fourth) child of the root.");
        assertEquals(currentNode, walker.currentNode(),
            "The worker should not just return the new node but also visit it. (3)");

        // Interesting step: moving to the previous sibling should yield the CopyAssignment 'i = j;'
        currentNode = walker.previousSibling();
        assertEquals(root.getChildAt(2), currentNode,
            "walker.previousSibling() should here return the second to last (third) child of the root.");
        assertEquals(currentNode, walker.currentNode(),
            "The worker should not just return the new node but also visit it. (4)");

        // Even more interesting: the previous node should now be deeper in the tree, namely a
        // descendant of the second LocalVariableDeclaration 'int j = 1:'
        // To be exact, it should be the IntLiteral '1'
        currentNode = walker.previousNode();
        assertEquals(IntLiteral.class, currentNode.getClass(),
            "The previous node should be an IntLiteral.");
        assertEquals(1, ((IntLiteral) currentNode).getValue(),
            "The previous node should be the IntLiteral '1'.");
        assertEquals(currentNode, walker.currentNode(),
            "The worker should not just return the new node but also visit it. (5)");

        // The next sibling should then be null, as the currentNode is the last node in the subtree
        // of 'int j = 1;'
        assertNull(walker.nextSibling(),
            "walker.nextSibling() should return null as there is no next sibling.");

        // Also interesting: the walker did not move, the next node should then again be the
        // CopyAssignment (third child) of the root
        currentNode = walker.nextNode();
        assertEquals(root.getChildAt(2), currentNode,
            "The next node should again be the third child of the root.");
    }
}
