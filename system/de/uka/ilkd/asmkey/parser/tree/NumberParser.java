// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.asmkey.parser.tree;


import de.uka.ilkd.asmkey.parser.env.EnvironmentException;
import de.uka.ilkd.asmkey.parser.env.TermEnvironment;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.Function;


/** This class translates textual numbers into the internal term
 * representations.
 *
 * @author Hubert Schmid */

final class NumberParser {

    /** Short reference to used term factory. */
    private static final TermFactory tf = TermFactory.DEFAULT;


    /** Return 'true' iff the given text is a number, i.e. it contains
     * only of digits. */
    public static boolean isNumber(String text) {
        if (text.length() == 0) {
            return false;
        }
        for (int i = 0; i < text.length(); ++i) {
            char ch = text.charAt(i);
            if (ch < '0' || ch > '9') {
                return false;
            }
        }
        return true;
    }

    /** Translate the given string into a number term. The environment
     * have to contain the defintions of the digits. */
    public static Term parseNumber(TermEnvironment env, String text) throws EnvironmentException {
        Term t = tf.createFunctionTerm((Function) env.getOperator(new Name("#")));
        for (int i = 0; i < text.length(); ++i) {
            char ch = text.charAt(i);
            if (ch < '0' || ch > '9') {
                throw new IllegalArgumentException("illegal number format");
            }
            t = tf.createFunctionTerm((Function) env.getOperator(new Name("" + ch)), t);
        }
        t = tf.createFunctionTerm((Function) env.getOperator(new Name("z")), t);
        return t;
    }

}
