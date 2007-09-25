// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof.init;

import de.uka.ilkd.key.casetool.ModelMethod;


/**
 * The "PreservesOwnInv" proof obligation. 
 */
public class PreservesOwnInvPO extends PreservesInvPO {
    
    public PreservesOwnInvPO(ModelMethod modelMethod, 
                             InvariantSelectionStrategy invStrategy) {
        super("PreservesOwnInv",
              modelMethod, 
              invStrategy,
              modelMethod.getContainingClass().getMyClassInvariants());
    }
}
