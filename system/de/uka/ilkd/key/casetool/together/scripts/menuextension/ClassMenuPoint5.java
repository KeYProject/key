// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.casetool.together.scripts.menuextension;

import de.uka.ilkd.key.casetool.together.FunctionalityOnModel;
import de.uka.ilkd.key.casetool.together.TogetherModelClass;
import de.uka.ilkd.key.proof.init.ProofInputException;


public class ClassMenuPoint5 extends ClassMenu {
    public String getMenuEntry(){
        return "BehaviouralSubtypingInv";
    }


    protected String runCore(TogetherModelClass modelClass)
    		throws ProofInputException {
        FunctionalityOnModel.proveBehaviouralSubtypingInv(modelClass);
        return "";
    }
}
