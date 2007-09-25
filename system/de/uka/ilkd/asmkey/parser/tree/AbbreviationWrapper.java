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


import de.uka.ilkd.asmkey.parser.env.AbbreviationMap;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.pp.AbbrevMap;


/** Implements an AbbreviationMap with an {@link
 * de.uka.ilkd.asmkey.parser.env.AbbreviationMap}. The queries are
 * forwarded to the corresponding methods in the actual abbreviation
 * map.
 *
 * @author Hubert Schmid */

final class AbbreviationWrapper implements AbbreviationMap {

    /** Stores the actual abbreviation map. */
    private final AbbrevMap abbrevMap;


    AbbreviationWrapper(AbbrevMap abbrevMap) {
        this.abbrevMap = abbrevMap;
    }


    public boolean containsAbbreviation(String name) {
        return abbrevMap.containsAbbreviation(name);
    }

    public Term getTerm(String name) {
        return abbrevMap.getTerm(name);
    }

}
