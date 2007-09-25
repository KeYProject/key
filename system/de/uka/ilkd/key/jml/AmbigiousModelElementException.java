// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2003 Universitaet Karlsruhe, Germany
//                         and Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//

package de.uka.ilkd.key.jml;

import de.uka.ilkd.key.logic.op.TermSymbol;

public class AmbigiousModelElementException extends Exception {

    public AmbigiousModelElementException(String errorMsg){
	super(errorMsg);
    }

    public AmbigiousModelElementException(TermSymbol op){
	this("ambigious declarations of "+op.name());
    }

}
