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


/**
 * Interface for position modifiers. A position modifier is a function which
 * gets a position and delivers a (new) position as result.
 *
 * @author christoph
 */
interface Modifier {
    /**
     * Function which delivers a new position based on pos.
     *
     * @param pos the position to be modified
     * @return the (new) position
     */
    PosInOccurrence modifyPosistion(PosInOccurrence pos);
}
