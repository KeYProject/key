package de.uka.ilkd.key.speclang;

import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.ProgramVariable;

/**
 * A replacement map for variables.
 */
public class VariableReplacementMap extends ReplacementMap<ProgramVariable> {

    public VariableReplacementMap(TermFactory tf) {
        super(tf);
    }

    @Override
    protected ProgramVariable convert(ProgramVariable variable, TermServices services) {
        return variable;
    }

}
