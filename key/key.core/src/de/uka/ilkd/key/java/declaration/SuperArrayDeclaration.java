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

package de.uka.ilkd.key.java.declaration;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.logic.ProgramElementName;

/**
 * At the moment the mere purpose of this Class is to provide an encapsulation
 * for the length attribute.
 */
public class SuperArrayDeclaration extends TypeDeclaration{
    
    private FieldDeclaration length = null;
        
    private SuperArrayDeclaration(ProgramElementName name, 
				  FieldDeclaration length) {
	super(new Modifier[0], 
	      name, name,
	      new MemberDeclaration[]{length},
	      false, false);
	this.length = length;
    }

    public SuperArrayDeclaration(FieldDeclaration length){
	this(new ProgramElementName("SuperArray"), length);
    }

    public int getChildCount(){
	return 0;
    }

    public boolean isInterface(){
	return false;
    }

    public FieldDeclaration length() {
	return length;
    }

    /** 
     * returns the local declared supertypes
     */
    public ImmutableList<KeYJavaType> getSupertypes() {
	return ImmutableSLList.<KeYJavaType>nil();
    }


    public ProgramElement getChildAt(int i){
	return null;
    }

    /** 
     * calls the corresponding method of a visitor in order to
     * perform some action/transformation on this element
     * @param v the Visitor
     */
    public void visit(Visitor v) {
	v.performActionOnSuperArrayDeclaration(this);
    }

}