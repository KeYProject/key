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


package de.uka.ilkd.key.java.recoderext;

import recoder.java.declaration.AnnotationUseSpecification;
import recoder.java.reference.TypeReference;

//HACK: This class is declared due to a bug in recoder causing a stack overflow when
//deepClone@AnnotationUseSpecification is called
public class KeYAnnotationUseSpecification extends AnnotationUseSpecification {

    /**
     * 
     */
    private static final long serialVersionUID = 2163251956161988258L;

    public KeYAnnotationUseSpecification(){
        super();
    }
    
    public KeYAnnotationUseSpecification(TypeReference tr){
        super(tr);
    }
    
    public KeYAnnotationUseSpecification deepClone(){
        return new KeYAnnotationUseSpecification(getTypeReference());
    }
    
}
