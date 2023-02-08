/* This file is part of KeY - https://key-project.org
 * KeY is licensed by the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0 */
package de.uka.ilkd.key.strategy.termfeature;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;

/**
 * this termfeature returns <tt>ZERO</tt> costs if the given term is non-rigid
 */
public class IsNonRigidTermFeature extends BinaryTermFeature {

    public static final TermFeature INSTANCE = new IsNonRigidTermFeature();

    private IsNonRigidTermFeature() {}

    protected boolean filter(Term term, Services services) {
        return !term.isRigid();
    }

}
