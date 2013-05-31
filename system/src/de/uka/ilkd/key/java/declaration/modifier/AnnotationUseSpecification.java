// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 


package de.uka.ilkd.key.java.declaration.modifier;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.declaration.Modifier;
import de.uka.ilkd.key.java.reference.TypeReference;
import de.uka.ilkd.key.java.reference.TypeReferenceContainer;

public class AnnotationUseSpecification extends Modifier implements TypeReferenceContainer{

    protected final TypeReference tr;
    
    public AnnotationUseSpecification(TypeReference tr){
        super();
        this.tr = tr;
    }
    
    protected String getSymbol(){
        return "@"+tr.toString();
    }

    public TypeReference getTypeReferenceAt(int index) {
        if(index==0){
            return tr;
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    public int getTypeReferenceCount() {
        return 1;
    }

    public ProgramElement getChildAt(int index) {
        if(index==0){
            return tr;
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    public int getChildCount() {
        return 1;
    }

}
