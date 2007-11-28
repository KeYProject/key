// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof.mgt;

import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.logic.SetOfLocationDescriptor;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Modality;

/**
 * @deprecated
 */
public interface HoareTripleContract extends Contract{

    Term getPre();

    Term getPost();

    SetOfLocationDescriptor getModifies();

    Modality getModality();    

    Statement getStatement();

}
