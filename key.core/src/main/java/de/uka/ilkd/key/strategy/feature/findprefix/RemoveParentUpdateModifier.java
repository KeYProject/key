/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.feature.findprefix;

import de.uka.ilkd.key.logic.op.UpdateApplication;

import org.key_project.prover.sequent.PosInOccurrence;


/**
 * If the parent operator of the find term is an update application, then change the position (on
 * which the checkers are applied) to the parent operator. Repeat until parent is no update
 * application.
 *
 * @author christoph
 */
public class RemoveParentUpdateModifier implements Modifier {


    @Override
    public PosInOccurrence modifyPosition(PosInOccurrence pos) {
        if (!pos.isTopLevel() && pos.up().subTerm().op() instanceof UpdateApplication) {
            return modifyPosition(pos.up());
        } else {
            return pos;
        }
    }

}
