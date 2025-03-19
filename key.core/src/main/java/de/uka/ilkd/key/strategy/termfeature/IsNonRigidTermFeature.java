/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.termfeature;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.strategy.feature.MutableState;

/**
 * this termfeature returns <tt>ZERO</tt> costs if the given term is non-rigid
 */
public class IsNonRigidTermFeature extends BinaryTermFeature {

    public static final TermFeature INSTANCE = new IsNonRigidTermFeature();

    private IsNonRigidTermFeature() {}

    @Override
    protected boolean filter(Term term, MutableState mState, Services services) {
        return !term.isRigid();
    }

}
