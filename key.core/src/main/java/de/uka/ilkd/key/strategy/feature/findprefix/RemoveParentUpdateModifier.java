/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.feature.findprefix;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.op.UpdateApplication;


/**
 * If the parent operator of the find term is an update application, then change the position (on
 * which the checkers are applied) to the parent operator. Repeat until parent is no update
 * application.
 *
 * @author christoph
 */
public class RemoveParentUpdateModifier implements Modifier {


    @Override
    public PosInOccurrence modifyPosistion(PosInOccurrence pos) {
        if (!pos.isTopLevel() && pos.up().subTerm().op() instanceof UpdateApplication) {
            return modifyPosistion(pos.up());
        } else {
            return pos;
        }
    }

}
