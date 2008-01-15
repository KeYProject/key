// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.casetool.together.scripts.menuextension;

import de.uka.ilkd.key.casetool.together.FunctionalityOnModel;
import de.uka.ilkd.key.casetool.together.TogetherModelMethod;
import de.uka.ilkd.key.proof.init.ProofInputException;


/**
 * The context menu item in Together for computing the specification of a method.
 * This user-interface element initiates the computation.
 * @author Andr&eacute; Platzer
 * @version 1.0, 2003-02-24
 * @stereotype UI
 * @see de.uka.ilkd.key.cspec.ComputeSpecification
 */
public class OpMenuPoint3 extends OpMenu {
    public String getMenuEntry(){
	return "ComputeSpecification";
    }

    public String getSubMenuName(){
	return null;
    }

    protected String runCore(TogetherModelMethod modelMethod)
    		throws ProofInputException {
        FunctionalityOnModel.computeSpecification(modelMethod);
        return "";
    }
}
