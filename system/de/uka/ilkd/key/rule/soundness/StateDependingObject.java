// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//


package de.uka.ilkd.key.rule.soundness;

import de.uka.ilkd.key.java.abstraction.ArrayOfKeYJavaType;
import de.uka.ilkd.key.logic.op.NonRigid;



public interface StateDependingObject extends NonRigid {

    //    public ListOfProgramVariable getInfluencingPV ();

    ArrayOfKeYJavaType getInfluencingPVTypes ();

}
