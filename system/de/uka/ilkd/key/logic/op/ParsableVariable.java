// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

/** this interface represents the variables that can be recognized 
 * by one of the parsers. */
package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.logic.sort.Sort;
public interface ParsableVariable extends Operator{

    /** @return Sort of the ParsableVariable */
    Sort sort();
}
