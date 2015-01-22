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
    public FormulaTermLabel parseInstance(List<String> parameters) throws TermLabelException {
        if (parameters == null || parameters.size() != 2) {
            throw new TermLabelException("Label " + FormulaTermLabel.NAME +
                    " requires exactly two Integer-Parameter with its ID and sub ID.");
        }
        Integer id;
        try {
            id = Integer.valueOf(parameters.get(0));
        } catch (NumberFormatException e) {
            throw new TermLabelException("Label " + FormulaTermLabel.NAME +
                  " requires exactly two Integer-Parameter with its ID and sub ID.", e);
        }
        Integer subId;
        try {
           subId = Integer.valueOf(parameters.get(1));
        } catch (NumberFormatException e) {
            throw new TermLabelException("Label " + FormulaTermLabel.NAME +
                  " requires exactly two Integer-Parameter with its ID and sub ID.", e);
        }
        return new FormulaTermLabel(id, subId);
    }
}