/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic;

import org.key_project.util.collection.ImmutableList;

/**
 * Records the changes made to a semisequent. Keeps track of added and removed formula to the
 * semisequents.
 */
public class SemisequentChangeInfo
        extends org.key_project.ncore.sequent.SemisequentChangeInfo<SequentFormula> {
    public SemisequentChangeInfo() {
        super();
    }

    public SemisequentChangeInfo(ImmutableList<SequentFormula> formulas) {
        super(formulas);
    }

    private SemisequentChangeInfo(SemisequentChangeInfo o) {
        super(o);
    }

    @Override
    public SemisequentChangeInfo copy() {
        return new SemisequentChangeInfo(this);
    }

    /**
     * returns the semisequent that is the result of the change operation
     */
    public Semisequent semisequent() {
        final Semisequent semisequent;
        if (modifiedSemisequent().isEmpty()) {
            semisequent = Semisequent.EMPTY_SEMISEQUENT;
        } else {
            semisequent = new Semisequent(modifiedSemisequent());
        }
        return semisequent;
    }
}
