/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package de.uka.ilkd.key.strategy.feature.findprefix;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.op.UpdateApplication;


/**
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
