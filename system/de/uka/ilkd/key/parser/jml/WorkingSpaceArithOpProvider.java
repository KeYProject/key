// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//


package de.uka.ilkd.key.parser.jml;

import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.op.Function;

public class WorkingSpaceArithOpProvider extends DefaultArithOpProvider{

    public WorkingSpaceArithOpProvider(Namespace functions, boolean javaSemantics){
	super(functions, javaSemantics);
    }

    public Function getAdd(boolean l){
	return getFunction(l, "add", "add", "add", "addition");
    }

    public Function getSub(boolean l){
	return getFunction(l, "sub", "sub", "sub", "subtraction");
    }

    public Function getMinus(boolean l){
	return getFunction(l, "neg", "neg", "neg", 
			   "negation");
    }

    public Function getMul(boolean l){
	return getFunction(l, "mul", "mul", "mul", "multiplication");
    }

    public Function getDiv(boolean l){
	return getFunction(l, "jdiv", "jdiv", "jdiv", "division");
    }

    public Function getMod(boolean l){
	return getFunction(l, "jmod", "jmod", "jmod", "modulo");
    }
}
