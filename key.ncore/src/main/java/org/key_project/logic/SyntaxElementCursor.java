/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.logic;

import java.util.ArrayDeque;
import java.util.Deque;

public class SyntaxElementCursor {
    record ParentAndPosition(SyntaxElement parent, int index) {}

    private final Deque<ParentAndPosition> path = new ArrayDeque<>();

    private SyntaxElement node;

    SyntaxElementCursor(SyntaxElement node) {
        this.node = node;
    }

    public SyntaxElement getCurrentNode() {
        return node;
    }

    public boolean gotoFirstChild() {
        if (node.getSyntaxChildCount() <= 0)
            return false;
        path.push(new ParentAndPosition(node, 0));
        node = node.getChild(0);
        return true;
    }

    public boolean gotoNextSibling() {
        if (path.isEmpty())
            return false;
        var pnp = path.pop();
        SyntaxElement parent = pnp.parent;
        int index = pnp.index + 1;
        if (index > parent.getSyntaxChildCount()) {
            return false;
        }
        path.push(new ParentAndPosition(parent, index));
        node = parent.getChild(index);
        return true;
    }

    public boolean gotoParent() {
        if (path.isEmpty())
            return false;
        node = path.pop().parent;
        return true;
    }
}
