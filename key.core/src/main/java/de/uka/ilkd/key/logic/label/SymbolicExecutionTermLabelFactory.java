/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic.label;

import java.util.List;

import de.uka.ilkd.key.logic.TermServices;

/**
 * A factory for creating {@link SymbolicExecutionTermLabel} objects.
 */
public class SymbolicExecutionTermLabelFactory
        implements TermLabelFactory<SymbolicExecutionTermLabel> {
    /**
     * {@inheritDoc}
     *
     * <p>
     * This method accepts single arguments which can be parsed as an integer.
     */
    @Override
    public SymbolicExecutionTermLabel parseInstance(List<String> parameters, TermServices services)
            throws TermLabelException {
        if (parameters == null || parameters.size() != 1) {
            throw new TermLabelException("Label " + SymbolicExecutionTermLabel.NAME
                + " requires exactly one Integer-Parameter with its ID.");
        }
        int val;
        try {
            val = Integer.parseInt(parameters.get(0));
        } catch (NumberFormatException e) {
            throw new TermLabelException("Label " + SymbolicExecutionTermLabel.NAME
                + " requires exactly one Integer-Parameter with its ID.", e);
        }

        return new SymbolicExecutionTermLabel(val);
    }
}
