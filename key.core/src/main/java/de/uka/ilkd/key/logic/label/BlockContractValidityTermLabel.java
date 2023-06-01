package de.uka.ilkd.key.logic.label;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.op.ProgramVariable;

/**
 * Label attached to the modality of the validity branch of a block contract.
 */
public class BlockContractValidityTermLabel implements TermLabel {
    /**
     * The unique name of this label.
     */
    public static final Name NAME = new Name("BC");

    /**
     * The name of the exception variable to distinguish normal from exceptional termination.
     */
    private final ProgramVariable exceptionVariable;

    /**
     * Constructor.
     *
     * @param exceptionVariable the exception variable to distinguish normal from exceptional
     *        termination.
     */
    public BlockContractValidityTermLabel(ProgramVariable exceptionVariable) {
        this.exceptionVariable = exceptionVariable;
    }

    /**
     * {@inheritDoc}
     */
    public String toString() {
        return NAME + "(" + getExceptionVariable() + ")";
    }

    /**
     * retrieves the original exception variable as found in the local variable declaration
     * statement
     *
     * @return the original exception variable
     */
    public ProgramVariable getExceptionVariable() {
        return exceptionVariable;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public ProgramVariable getChild(int i) {
        switch (i) {
        case 0:
            return getExceptionVariable();
        default:
            return null;
        }
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public int getChildCount() {
        return 1;
    }



    /**
     * {@inheritDoc}
     */
    @Override
    public Name name() {
        return NAME;
    }

}
