//This file is part of KeY - Integrated Deductive Software Design
//Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                    Universitaet Koblenz-Landau, Germany
//                    Chalmers University of Technology, Sweden
//
//The KeY system is protected by the GNU General Public License. 
//See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.casetool.together.scripts.menuextension;

import de.uka.ilkd.key.casetool.together.FunctionalityOnModel;
import de.uka.ilkd.key.casetool.together.TogetherModelMethod;
import de.uka.ilkd.key.proof.init.ProofInputException;


public class OpMenuPoint11 extends OpMenu {
    public String getMenuEntry() {
        return "PreservesGuard";
    }
    
    public String getSubMenuName() {
        return "vertical";
    }
    
    protected String runCore(TogetherModelMethod modelMethod) 
                throws ProofInputException {
        FunctionalityOnModel.provePreservesGuard(modelMethod);
        return "";
    }
}
