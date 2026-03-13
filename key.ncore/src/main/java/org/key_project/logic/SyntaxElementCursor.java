/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.logic;

import java.util.ArrayDeque;
import java.util.Deque;

/// A cursor (or walker) for navigating [SyntaxElement]s in pre-order.
public class SyntaxElementCursor {

    public boolean hasNext() {
        return !path.isEmpty() || node.getChildCount() > 0;
    }

    private record ParentAndPosition(SyntaxElement parent, int index) {
    }

    private final Deque<ParentAndPosition> path = new ArrayDeque<>();

    private SyntaxElement node;

    SyntaxElementCursor(SyntaxElement node) {
        this.node = node;
    }

    public SyntaxElement getCurrentNode() {
        return node;
    }

    /// Advance the cursor to the current node's first child if possible.
    /// Otherwise, no changes to the state occur.
    ///
    /// @return true iff the current node has at least one child.
    public boolean gotoFirstChild() {
        if (node.getChildCount() <= 0)
            return false;
        path.push(new ParentAndPosition(node, 0));
        node = node.getChild(0);
        return true;
    }

    /// Advance the cursor to the current node's next sibling if possible.
    /// Otherwise, no changes to the state occur.
    ///
    /// @return true iff the current node has at least one sibling not yet visited.
    public boolean gotoNextDirectSibling() {
        if (path.isEmpty())
            return false;
        var pnp = path.pop();
        SyntaxElement parent = pnp.parent;
        int index = pnp.index + 1;
        if (index >= parent.getChildCount()) {
            path.push(pnp);
            return false;
        }
        path.push(new ParentAndPosition(parent, index));
        node = parent.getChild(index);
        return true;
    }

    /// Advance the cursor to the current node's next sibling if possible.
    /// If no direct sibling exists, go up one step and try again.
    /// Otherwise, no changes to the state occur.
    ///
    /// @return true iff the current node has at least one sibling not yet visited.
    public boolean gotoNextSibling() {
        if (gotoNextDirectSibling())
            return true;
        var ancestors = new ArrayDeque<ParentAndPosition>();
        while (!path.isEmpty()) {
            ancestors.add(path.pop());
            if (gotoNextDirectSibling())
                return true;
        }
        // Nothing found; re-build stack
        for (var ancestor : ancestors) {
            path.push(ancestor);
        }
        return false;
    }

    /// Advance the cursor to the current node's parent if possible.
    /// Otherwise, no changes to the state occur.
    ///
    /// @return true iff the current node is not the root.
    public boolean gotoParent() {
        if (path.isEmpty())
            return false;
        node = path.pop().parent;
        return true;
    }

    /// Advance cursor to the next node.
    /// If the node has children, the cursor advances to the first child.
    /// Otherwise, if the node has unvisited siblings, the cursor advances to the next unvisited
    /// sibling.
    /// Otherwise, no changes to the state.
    ///
    /// @return true iff the node has children or an unvisited sibling.
    public boolean goToNext() {
        var ancestors = new ArrayDeque<ParentAndPosition>();
        if (gotoFirstChild())
            return true;
        if (gotoNextDirectSibling())
            return true;
        while (!path.isEmpty()) {
            ancestors.add(path.pop());
            if (gotoNextDirectSibling())
                return true;
        }
        // Nothing found; re-build stack
        for (var ancestor : ancestors) {
            path.push(ancestor);
        }
        return false;
    }
}
