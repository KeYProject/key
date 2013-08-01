// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//
package de.uka.ilkd.key.strategy.feature.findprefix;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.op.UpdateApplication;


/**
 * If the parent operator of the find term is an update application,
 * then change the position (on which the checkers are applied)
 * to the parent operator. Repeat until parent is no update
 * application.
 * 
 * @author christoph
 */
public class RemoveParentUpdateModifier implements Modifier {


    @Override
    public PosInOccurrence modifyPosistion(PosInOccurrence pos) {
        if (!pos.isTopLevel() &&
            pos.up().subTerm().op() instanceof UpdateApplication) {
            return modifyPosistion(pos.up());
        } else {
            return pos;
        }
    }

}
