/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.rule;

import org.key_project.rusty.Services;

public class UninstantiatedNoPosTacletApp extends NoPosTacletApp {
    UninstantiatedNoPosTacletApp(Taclet taclet) {
        super(taclet);
    }

    @Override
    protected MatchConditions setupMatchConditions(PosInOccurrence pos, Services services) {
        if (taclet() instanceof RewriteTaclet rwt) {
            return rwt.checkPrefix(pos,
                MatchConditions.EMPTY_MATCHCONDITIONS);
        }

        return MatchConditions.EMPTY_MATCHCONDITIONS;
    }
}
