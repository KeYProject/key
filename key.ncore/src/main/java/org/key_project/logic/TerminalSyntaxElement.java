package org.key_project.logic;

public interface TerminalSyntaxElement extends SyntaxElement{
    @Override
    default SyntaxElement getChild(int n) {
        throw new IndexOutOfBoundsException(this.getClass() + " " + this + " has no children");
    }

    @Override
    default int getChildCount() {
        return 0;
    }
}
