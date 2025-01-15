/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.termfeature;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.label.ParameterlessTermLabel;
import de.uka.ilkd.key.strategy.feature.MutableState;

import org.key_project.logic.Term;
import org.key_project.logic.op.Function;


public final class AnonHeapTermFeature extends BinaryTermFeature {

    public static final AnonHeapTermFeature INSTANCE = new AnonHeapTermFeature();

    private AnonHeapTermFeature() {
    }

    @Override
    protected boolean filter(Term term, MutableState mState, Services services) {
        var t = (de.uka.ilkd.key.logic.Term) term;
        return // the heap term is an anon heap symbol
               // (for instance an anonHeap function)
        t.hasLabels() && t.containsLabel(ParameterlessTermLabel.ANON_HEAP_LABEL)
                && t.op().arity() == 0 && t.op() instanceof Function;
    }

}
