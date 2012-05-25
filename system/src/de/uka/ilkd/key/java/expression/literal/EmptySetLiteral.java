// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//


package de.uka.ilkd.key.java.expression.literal;

import de.uka.ilkd.key.java.NameAbstractionTable;
import de.uka.ilkd.key.java.PrettyPrinter;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.expression.Literal;
import de.uka.ilkd.key.java.visitor.Visitor;



public class EmptySetLiteral extends Literal {

    public static final EmptySetLiteral LOCSET = new EmptySetLiteral();
    public static final EmptySetLiteral UNTYPED = new EmptySetLiteral(false);
    
    private final boolean locSet;
    
    private EmptySetLiteral() {
    	locSet = true;
    }   
    
    private EmptySetLiteral(boolean isLocSetType){
    	locSet = isLocSetType;
    }
    
    
    @Override
    public boolean equalsModRenaming(SourceElement o, 
                                     NameAbstractionTable nat) {
	return o == this;
    }


    public void visit(Visitor v) {
	v.performActionOnEmptySetLiteral(this);
    }

    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
        p.printEmptySetLiteral(this);
    }


    public KeYJavaType getKeYJavaType(Services javaServ) {
	PrimitiveType type = locSet? PrimitiveType.JAVA_LOCSET : PrimitiveType.JAVA_SET;
	return javaServ.getJavaInfo().getKeYJavaType(type);
    }
}
