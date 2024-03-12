package de.uka.ilkd.key.java.statement;

import de.uka.ilkd.key.java.PositionInfo;
import org.key_project.util.ExtList;

public abstract class SwitchBranch extends BranchImp {
    public SwitchBranch() {
        super();
    }

    public SwitchBranch(ExtList children) {
        super(children);
    }

    public SwitchBranch(ExtList children, PositionInfo pos) {
        super(children, pos);
    }
}
