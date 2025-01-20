/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.smt;


import java.math.BigInteger;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.util.Debug;

/**
 * Translates a number into a string representation.
 */
public final class NumberTranslation {

    private NumberTranslation() {}

    /**
     * This methods translates a term with sort "numbers" into a BigInteger representing the number.
     *
     * @param term term with sort "numbers"
     * @return An instance of BigInteger representing the number
     */
    public static BigInteger translate(Term term) {
        if (!term.sort().name().toString().trim().equals("numbers")) {
            throw new IllegalArgumentException(
                "Only terms with sort \"numbers\" may be translated.\n" + "Term " + term
                    + " is  of sort " + term.sort().name().toString().trim());
        }
        Operator op = term.op();
        String name = op.name().toString();
        if (name.length() == 1) {
            char ch = name.charAt(0);
            if (ch >= '0' && ch <= '9') {
                Debug.assertTrue(term.arity() == 1);
                return translate(term.sub(0)).multiply(smallInts[10]).add(smallInts[ch - '0']);
            } else if (ch == '#') {
                Debug.assertTrue(term.arity() == 0);
                return BigInteger.ZERO;
            } else {
                Debug.fail("unknown number literal");
                return null; // not reached
            }
        } else if ("neglit".equals(name)) {
            Debug.assertTrue(term.arity() == 1);
            /*
             * Hint: translate operator "neg" at all places correctly, e.g. neg(1(neg(1(#)))).
             */
            return translate(term.sub(0)).negate();
        } else {
            Debug.fail("unknown number literal");
            return null; // not reached
        }
    }

    /* BigInteger instances for values 0..10 */
    private static final BigInteger[] smallInts;

    static {
        /* initialize smallInts */
        smallInts = new BigInteger[11];
        for (int i = 0; i < smallInts.length; ++i) {
            smallInts[i] = new BigInteger(String.valueOf(i));
        }
    }

}
