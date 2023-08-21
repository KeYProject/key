/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.TermServices;


/**
 * A subclass of <code>NoPosTacletApp</code> for the special case of a taclet app without any
 * instantiations. The method <code>setupMatchConditions</code> is overwritten to avoid object
 * creations.
 */
class UninstantiatedNoPosTacletApp extends NoPosTacletApp {

    /**
     * @param taclet
     */
    UninstantiatedNoPosTacletApp(Taclet taclet) {
        super(taclet);
    }

    /*
     * (non-Javadoc)
     *
     * @see de.uka.ilkd.key.rule.NoPosTacletApp#setupMatchConditions(de.uka.ilkd.key.logic.
     * PosInOccurrence, de.uka.ilkd.key.java.Services, de.uka.ilkd.key.logic.Constraint)
     */
    @Override
    protected MatchConditions setupMatchConditions(PosInOccurrence pos, TermServices services) {
        if (taclet() instanceof RewriteTaclet) {
            return ((RewriteTaclet) taclet()).checkPrefix(pos,
                MatchConditions.EMPTY_MATCHCONDITIONS);
        }

        return MatchConditions.EMPTY_MATCHCONDITIONS;
    }
}
