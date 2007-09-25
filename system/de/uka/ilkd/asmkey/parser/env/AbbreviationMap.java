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


import de.uka.ilkd.key.logic.Term;


/** The abbreviation map contains mappings from identifiers to terms.
 *
 * @author Hubert Schmid */

public interface AbbreviationMap {

    /** Check if an abbreviation with the given name exists. */
    boolean containsAbbreviation(String name);

    /** Return the term that is abbreviated by this name. */
    Term getTerm(String name);

}
