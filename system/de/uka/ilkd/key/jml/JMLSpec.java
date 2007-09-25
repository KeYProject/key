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

import java.util.LinkedHashMap;

import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.parser.jml.NotSupportedExpressionException;

public abstract class JMLSpec extends TermBuilder {

    protected Namespace progVarNS = null;
    protected Namespace funcNS = null;
    protected NotSupportedExpressionException nsEx = null;

    public abstract LinkedHashMap getTerm2Old();

    public Namespace getProgramVariableNS(){
	return progVarNS;
    }

    public Namespace getFunctionNS(){
	return funcNS;
    }

    public void setInvalid(NotSupportedExpressionException nsEx){
	this.nsEx = nsEx;
    }

    public boolean isValid(){
	return nsEx == null;
    }

}
