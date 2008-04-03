package de.uka.ilkd.key.util;

import de.uka.ilkd.key.logic.op.ProgramMethod;

public class PositionWrapper {
    
    private ProgramMethod programMethod;
    private int position;

    public PositionWrapper(ProgramMethod programMethod, int position) {
        super();
        this.programMethod = programMethod;
        this.position = position;
    }
    
    
    public ProgramMethod getProgramMethod() {
        return programMethod;
    }

    public int getPosition() {
        return position;
    }

}
