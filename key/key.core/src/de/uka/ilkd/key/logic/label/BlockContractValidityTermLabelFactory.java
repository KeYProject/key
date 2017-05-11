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

import org.key_project.util.java.ObjectUtil;
import org.key_project.util.java.StringUtil;

import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.ProgramVariable;

/**
 * A factory for creating {@link BlockContractValidityTermLabel} objects.
 */
public class BlockContractValidityTermLabelFactory implements TermLabelFactory<BlockContractValidityTermLabel> {
    /**
     * {@inheritDoc}
     *
     * <p>
     * This method accepts single arguments which can be parsed as a {@link String}.
     */
    @Override
    public BlockContractValidityTermLabel parseInstance(List<String> parameters, TermServices services) throws TermLabelException {
        if (parameters == null || parameters.size() != 1) {
            throw new TermLabelException("Label " + BlockContractValidityTermLabel.NAME +
                    " requires exactly one String-Parameter with the name of the exception variable.");
        }
        String val = ObjectUtil.toString(parameters.get(0));
        if (StringUtil.isTrimmedEmpty(val)) {
           throw new TermLabelException("Label " + BlockContractValidityTermLabel.NAME +
                 " requires exactly one String-Parameter with the name of the exception variable.");
        }
        return new BlockContractValidityTermLabel((ProgramVariable) services.getNamespaces().programVariables().lookup(val));
    }
}