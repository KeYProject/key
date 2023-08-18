/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.logic.op.Operator;

/**
 * This feature returns zero if and only if the focus of the given rule application exists, is not
 * top-level and the symbol immediately above the focus is <code>badSymbol</code>. Optionally, one
 * can also specify that zero should only be returned if the symbol immediately above the focus is
 * <code>badSymbol</code> and the focus has a certain subterm index.
 *
 * TODO: eliminate this class and use term features instead
 */
public class DirectlyBelowSymbolFeature extends DirectlyBelowFeature {


    private DirectlyBelowSymbolFeature(Operator badSymbol, int index) {
        super(badSymbol, index);
    }

    public static Feature create(Operator badSymbol) {
        return new DirectlyBelowSymbolFeature(badSymbol, -1);
    }

    public static Feature create(Operator badSymbol, int index) {
        return new DirectlyBelowSymbolFeature(badSymbol, index);
    }

    protected boolean isBadSymbol(Operator op) {
        return badSymbol == op;
    }


}
