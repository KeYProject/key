/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.label;

import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.label.TermLabelContext;


/**
 * This policy always maintains a label.
 *
 * @author lanzinger
 */
public class PerpetualTermLabelPolicy implements TermLabelPolicy {

    @Override
    public TermLabel keepLabel(TermLabelContext context, JTerm sourceTerm, JTerm newTerm,
            TermLabel label) {
        return label;
    }
}
