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


/** Exception signals that a term is not valid
 * usullay rethrown as ParserException with location
 * information
 *
 * @author Stanislas Nanchen 
 */

public final class TermNotValidException extends Exception {

    public TermNotValidException(String message) {
        super(message);
    }

}
