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
        if (node.getChildCount() <= 0) return false;
        path.push(new ParentAndPosition(node, 0));
        node = node.getChild(0);
        return true;
    }

    public boolean gotoNextSibling() {
        if (path.isEmpty()) return false;
        var pnp = path.pop();
        SyntaxElement parent = pnp.parent;
        int index =pnp.index+1;
        if (index > parent.getChildCount()) {
            return false;
        }
        path.push(new ParentAndPosition(parent, index));
        node = parent.getChild(index);
        return true;
    }

    public boolean gotoParent() {
        if (path.isEmpty()) return false;
        node = path.pop().parent;
        return true;
    }
}
