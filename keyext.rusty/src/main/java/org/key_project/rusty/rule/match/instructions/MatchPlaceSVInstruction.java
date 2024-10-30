/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.rule.match.instructions;

import org.key_project.logic.SyntaxElementCursor;
import org.key_project.logic.Term;
import org.key_project.rusty.Services;
import org.key_project.rusty.logic.PVPlace;
import org.key_project.rusty.logic.SVPlace;
import org.key_project.rusty.logic.op.MutRef;
import org.key_project.rusty.logic.op.sv.ProgramSV;
import org.key_project.rusty.rule.MatchConditions;

import org.jspecify.annotations.NonNull;

public class MatchPlaceSVInstruction extends MatchSchemaVariableInstruction<@NonNull ProgramSV> {
    public MatchPlaceSVInstruction(SVPlace place) {
        super(place.getSchemaVariable());
    }

    public MatchConditions match(MutRef mr, MatchConditions mc, Services services) {
        var place = mr.getPlace();
        if (place instanceof PVPlace pvp) {
            return addInstantiation(services.getTermBuilder().var(pvp.getProgramVariable()), mc,
                services);
        }
        return null;
    }

    @Override
    public MatchConditions match(SyntaxElementCursor cursor, MatchConditions matchConditions,
            Services services) {
        cursor.goToNext();
        var node = cursor.getCurrentNode();
        if (!(node instanceof MutRef mr))
            return null;
        final MatchConditions result =
            match(mr, matchConditions, services);
        if (result != null) {
            cursor.gotoNextSibling();
        }
        return result;
    }

    @Override
    public MatchConditions match(Term instantiationCandidate, MatchConditions matchCond,
            Services services) {
        return match((MutRef) instantiationCandidate.op(), matchCond, services);
    }
}
