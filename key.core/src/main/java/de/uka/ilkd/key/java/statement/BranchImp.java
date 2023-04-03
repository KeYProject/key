package de.uka.ilkd.key.java.statement;

import de.uka.ilkd.key.java.JavaNonTerminalProgramElement;
import de.uka.ilkd.key.java.PositionInfo;

import org.key_project.util.ExtList;

/**
 * Branch.
 *
 * @author <TT>AutoDoc</TT>
 */

public abstract class BranchImp extends JavaNonTerminalProgramElement implements Branch {

    /**
     * Constructor for the transformation of COMPOST ASTs to KeY.
     *
     * @param children the children of this AST element as KeY classes. May contain: Comments
     */
    public BranchImp(ExtList children) {
        super(children);
    }


    public BranchImp() {
        super();
    }


    public BranchImp(ExtList children, PositionInfo pos) {
        super(children, pos);
    }


}
