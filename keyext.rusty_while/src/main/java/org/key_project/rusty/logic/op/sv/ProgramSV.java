package org.key_project.rusty.logic.op.sv;

import org.jspecify.annotations.NonNull;
import org.key_project.logic.Name;
import org.key_project.logic.SyntaxElement;
import org.key_project.rusty.logic.sort.ProgramSVSort;

public final class ProgramSV extends OperatorSV implements SyntaxElement {
    private final boolean isListSV;

    /**
     * creates a new SchemaVariable used as a placeholder for program constructs
     *
     * @param name the Name of the SchemaVariable allowed to match a list of program constructs
     */
    ProgramSV(Name name, ProgramSVSort s, boolean isListSV) {
        super(name, s, false, false);
        this.isListSV = isListSV;
    }

    public boolean isListSV() {
        return isListSV;
    }

    @Override
    public  @NonNull SyntaxElement getChild(int n) {
        throw new IndexOutOfBoundsException("ProgramSV " + this + " has no children");
    }

    @Override
    public int getChildCount() {
        return 0;
    }
}
