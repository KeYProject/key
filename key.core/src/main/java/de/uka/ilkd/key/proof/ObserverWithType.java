/* This file is part of KeY - https://key-project.org
 * KeY is licensed by the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0 */
package de.uka.ilkd.key.proof;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.op.IObserverFunction;

/**
 *
 * @author christoph
 */
public class ObserverWithType {

    public final KeYJavaType kjt;
    public final IObserverFunction obs;

    public ObserverWithType(KeYJavaType kjt, IObserverFunction obs) {
        this.kjt = kjt;
        this.obs = obs;
    }

    @Override
    public boolean equals(Object obj) {
        if (obj instanceof ObserverWithType && obj != null) {
            ObserverWithType o = (ObserverWithType) obj;
            return kjt.equals(o.kjt) && obs.equals(o.obs);
        } else {
            return false;
        }
    }

    @Override
    public int hashCode() {
        int hash = 7;
        hash = 53 * hash + (this.kjt != null ? this.kjt.hashCode() : 0);
        hash = 53 * hash + (this.obs != null ? this.obs.hashCode() : 0);
        return hash;
    }
}
