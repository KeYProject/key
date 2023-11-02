/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.reference;

import java.util.Collection;

import de.uka.ilkd.key.logic.Sequent;

public class OneOfCondition implements Condition {
    private final Collection<Condition> inner;

    public OneOfCondition(Collection<Condition> inner) {
        this.inner = inner;
    }

    @Override
    public boolean isFulfilled(Sequent seq) {
        return inner.stream().anyMatch(x -> x.isFulfilled(seq));
    }
}
