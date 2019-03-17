// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

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
     * @param exceptionVariable the exception variable to distinguish normal from exceptional termination.
     */
    public BlockContractValidityTermLabel(ProgramVariable exceptionVariable) {
        this.exceptionVariable = exceptionVariable;
    }

    /**
     * {@inheritDoc}
     */
    public String toString() {
        return NAME.toString() + "(" + getExceptionVariable() + ")";
    }
    
    /**
     * retrieves the original exception variable as found in the local variable declaration statement
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
        case 0 : return getExceptionVariable();
        default : return null;
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
