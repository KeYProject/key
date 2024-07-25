package org.key_project.rusty.rule.inst;

import org.key_project.logic.SyntaxElement;
import org.key_project.rusty.ast.RustyProgramElement;
import org.key_project.util.collection.ImmutableArray;

public class ProgramList implements SyntaxElement {
    private final ImmutableArray<RustyProgramElement> list;

    public ProgramList(ImmutableArray<RustyProgramElement> list) {
        assert list != null
                : "Constructor of ProgramList must" + " not be called with null argument";
        this.list = list;
    }

    public ImmutableArray<RustyProgramElement> getList() {
        return list;
    }

    public boolean equals(Object o) {
        if (!(o instanceof ProgramList)) {
            return false;
        }
        return list.equals(((ProgramList) o).list);
    }

    public int hashCode() {
        return list.hashCode();
    }


    @Override
    public SyntaxElement getChild(int n) {
        return list.get(n);
    }

    @Override
    public int getChildCount() {
        return list.size();
    }
}
