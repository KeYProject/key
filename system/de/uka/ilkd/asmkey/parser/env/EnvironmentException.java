// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.asmkey.parser.env;


/** Exception signals environment errors (undefined variables, etc.).
 *
 * @author Hubert Schmid
 */

public final class EnvironmentException extends Exception {

    public EnvironmentException(String message) {
        super(message);
    }

}
