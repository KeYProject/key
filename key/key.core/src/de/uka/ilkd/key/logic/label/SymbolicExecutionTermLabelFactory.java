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

import java.util.List;

/**
 * A factory for creating {@link SymbolicExecutionTermLabel} objects.
 */
public class SymbolicExecutionTermLabelFactory implements TermLabelFactory<SymbolicExecutionTermLabel> {
    /**
     * {@inheritDoc}
     *
     * <p>
     * This method accepts single arguments which can be parsed as an integer.
     */
    @Override
    public SymbolicExecutionTermLabel parseInstance(List<String> parameters) throws TermLabelException {
        if (parameters == null || parameters.size() != 1) {
            throw new TermLabelException("Label " + SymbolicExecutionTermLabel.NAME +
                    " requires exactly one Integer-Parameter with its ID.");
        }
        Integer val;
        try {
            val = Integer.valueOf(parameters.get(0));
        } catch (NumberFormatException e) {
            throw new TermLabelException("Label " + SymbolicExecutionTermLabel.NAME +
                    " requires exactly one Integer-Parameter with its ID.", e);
        }

        return new SymbolicExecutionTermLabel(val);
    }
}