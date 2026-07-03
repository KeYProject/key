/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.label;

import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.label.TermLabelContext;
import de.uka.ilkd.key.logic.op.JavaDLOperatorUtil;

import org.key_project.logic.op.Operator;

/**
 * This {@link TermLabelPolicy} maintains a {@link TermLabel} as long the new {@link JTerm} has the
 * same {@link Operator} as the previous best matching {@link JTerm} from which it was created.
 *
 * @author Martin Hentschel
 */
public class StayOnOperatorTermLabelPolicy implements TermLabelPolicy {
    /**
     * {@inheritDoc}
     */
    @Override
    public TermLabel keepLabel(TermLabelContext context, JTerm sourceTerm, JTerm newTerm,
            TermLabel label) {
        return sourceTerm != null
                && JavaDLOperatorUtil.opEquals(newTerm.op(), sourceTerm.op())
                        ? label
                        : null;
    }
}
