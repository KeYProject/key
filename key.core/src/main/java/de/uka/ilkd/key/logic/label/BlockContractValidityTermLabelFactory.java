/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.logic.label;

import java.util.List;

import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.ProgramVariable;

import org.key_project.util.java.StringUtil;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * A factory for creating {@link BlockContractValidityTermLabel} objects.
 */
@NullMarked
public class BlockContractValidityTermLabelFactory
        implements TermLabelFactory<BlockContractValidityTermLabel> {
    /**
     * {@inheritDoc}
     *
     * <p>
     * This method accepts single arguments which can be parsed as a {@link String}.
     *
     * <p>
     * The {@code lookup} of the parsed exception-variable name may legitimately miss the
     * program-variable namespace, in which case it returns {@code null} and the parsed label
     * carries no exception variable (matching the pre-nullness-annotation behavior).
     * {@link BlockContractValidityTermLabel} keeps its {@code exceptionVariable} component
     * non-null; the null case is suppressed here and widening the record component is tracked
     * as follow-up work.
     */
    @SuppressWarnings("nullness:argument.type.incompatible")
    @Override
    public BlockContractValidityTermLabel parseInstance(@Nullable List<String> parameters,
            TermServices services) throws TermLabelException {
        if (parameters == null || parameters.size() != 1) {
            throw new TermLabelException("Label " + BlockContractValidityTermLabel.NAME
                + " requires exactly one String-Parameter with the name of the exception variable.");
        }
        String val = parameters.get(0);
        if (StringUtil.isTrimmedEmpty(val)) {
            throw new TermLabelException("Label " + BlockContractValidityTermLabel.NAME
                + " requires exactly one String-Parameter with the name of the exception variable.");
        }
        return new BlockContractValidityTermLabel(
            (ProgramVariable) services.getNamespaces().programVariables().lookup(val));
    }
}
