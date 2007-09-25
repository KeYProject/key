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

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.sort.Sort;


/** Interface for parsing.
 *
 * @author Hubert Schmid
 */

public interface SortEnvironment {

    /** Returns the sort with the given name.
     *
     * @throws EnvironmentException if no sort with this name is
     * declared.
     */
    Sort getSort(Name id) throws EnvironmentException;

}
