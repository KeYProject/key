// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.logic;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.logic.op.IProgramMethod;

public class MethodStackInfo implements NameCreationInfo {

    ImmutableList<IProgramMethod> methods;
    
    public MethodStackInfo(ImmutableList<IProgramMethod> methods) {
        this.methods = methods;
    }

    public String infoAsString() {
        String result = "Method stack:\n";

        for (IProgramMethod method : methods) {
            result += "- " + method.getProgramElementName().toString() + "\n";
        }

	if(result.length() < 1) return "";

        result = result.substring(0, result.length() - 1);

        return result;
    }

}