/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.logic;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;

public class SyntaxElementCursorTest {
    class Node implements SyntaxElement {
        private final int value;
        private final Node[] children;

        public Node(int value, Node... children) {
            this.value = value;
            this.children = children;
        }

        public int getValue() {
            return value;
        }

        @Override
        public int getChildCount() {
            return children.length;
        }

        @Override
        public SyntaxElement getChild(int n) {
            return children[n];
        }
    }

    private Node example1() {
        return new Node(0,
            new Node(1, new Node(2), new Node(3)),
            new Node(4, new Node(5), new Node(6)));
    }

    private List<Integer> traverse(Node n) {
        var lst = new ArrayList<Integer>();
        var cursor = n.getCursor();
        do {
            lst.add(((Node) cursor.getCurrentNode()).getValue());
        } while (cursor.goToNext());
        return lst;
    }

    @Test
    void testOrder() {
        var tree = example1();

        assertEquals(
            Arrays.asList(0, 1, 2, 3, 4, 5, 6),
            traverse(tree));
    }
}
