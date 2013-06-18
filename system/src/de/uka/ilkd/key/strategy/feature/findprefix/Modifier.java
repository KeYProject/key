/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package de.uka.ilkd.key.strategy.feature.findprefix;

import de.uka.ilkd.key.logic.PosInOccurrence;


/**
 *
 * @author christoph
 */
interface Modifier {
    PosInOccurrence modifyPosistion(PosInOccurrence pos);
}
