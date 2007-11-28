// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2004 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License.
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.logic;

import de.uka.ilkd.key.logic.op.IteratorOfProgramMethod;
import de.uka.ilkd.key.logic.op.ListOfProgramMethod;
import de.uka.ilkd.key.logic.op.ProgramMethod;

public class MethodStackInfo implements NameCreationInfo {

    ListOfProgramMethod methods;
    
    public MethodStackInfo(ListOfProgramMethod methods) {
        this.methods = methods;
    }

    public String infoAsString() {
        String result = "Method stack:\n";

        IteratorOfProgramMethod it = methods.iterator();
        while(it.hasNext()) {
            ProgramMethod m = it.next();
            result += "- " + m.getProgramElementName().toString() + "\n";
        }

	if(result.length() < 1) return "";

        result = result.substring(0, result.length() - 1);

        return result;
    }

}
