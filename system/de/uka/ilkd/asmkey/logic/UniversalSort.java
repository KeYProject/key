// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.asmkey.logic;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.sort.GenericSort;
import de.uka.ilkd.key.logic.sort.Sort;

/** Class with the universal sort, which is always ok.
 *
 * @author Stanislas Nanchen
 */

public class UniversalSort extends GenericSort {

    public static final Sort UNIVERSAL = new UniversalSort();

    private UniversalSort() {
	super (new Name("//UNIVERSAL"));
    }
}
