package de.uka.ilkd.key.java.recoderext;

import recoder.java.declaration.AnnotationUseSpecification;
import recoder.java.reference.TypeReference;

//HACK: This class is declared due to a bug in recoder causing a stack overflow when
//deepClone@AnnotationUseSpecification is called
public class KeYAnnotationUseSpecification extends AnnotationUseSpecification {

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
