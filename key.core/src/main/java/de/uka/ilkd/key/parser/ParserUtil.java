/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.parser;


import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.java.reference.*;
import de.uka.ilkd.key.parser.proofjava.Token;
import de.uka.ilkd.key.util.parsing.LocatableException;

import recoder.java.Expression;
import recoder.java.reference.UncollatedReferenceQualifier;

/**
 * @author Alexander Weigl
 * @version 1 (6/21/21)
 */
public final class ParserUtil {
    /**
     * Throws an exception if the given expression is invalid in a {@code \singleton} constructor.
     * The given token is used for positional information.
     */
    public static void checkValidSingletonReference(Expression expr, Token tok) {
        // weigl: I hope I catch them all.
        if (expr instanceof VariableReference || expr instanceof ThisReference
                || expr instanceof ArrayReference || expr instanceof ArrayLengthReference
                || expr instanceof UncollatedReferenceQualifier || expr instanceof SuperReference) {
            return;
        }
        Location loc = new Location(null, Position.fromToken(tok));
        throw new LocatableException("Given non-reference as parameter for \\singleton", loc);
    }
}
