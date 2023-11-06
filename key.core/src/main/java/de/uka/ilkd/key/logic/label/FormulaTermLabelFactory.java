/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic.label;

import java.util.List;

import de.uka.ilkd.key.logic.TermServices;

/**
 * A factory for creating {@link FormulaTermLabel} objects.
 */
public class FormulaTermLabelFactory implements TermLabelFactory<FormulaTermLabel> {
    /**
     * {@inheritDoc}
     *
     * <p>
     * This method accepts single arguments which can be parsed as an integer.
     */
    @Override
    public FormulaTermLabel parseInstance(List<String> parameters, TermServices services)
            throws TermLabelException {
        if (parameters != null && parameters.size() == 1) {
            return new FormulaTermLabel(parameters.get(0));
        } else if (parameters != null && parameters.size() == 2) {
            return new FormulaTermLabel(parameters.get(0), parameters.get(1));
        } else {
            throw new TermLabelException("Label " + FormulaTermLabel.NAME
                + " requires the unique ID as first parameter and an optional by semicolon separated list of parent IDs as second parameter.");
        }
    }
}
