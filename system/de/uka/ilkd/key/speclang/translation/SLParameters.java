package de.uka.ilkd.key.speclang.translation;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.ListOfKeYJavaType;
import de.uka.ilkd.key.java.abstraction.SLListOfKeYJavaType;

public class SLParameters {

    
    private final ListOfSLExpression parameters;

    public SLParameters(ListOfSLExpression parameters) {
        this.parameters = parameters;
    }
    
    public ListOfSLExpression getParameters() {
        return parameters;
    }
    
    
    public boolean isListOfTerm() {
        
        IteratorOfSLExpression it = parameters.iterator();
        
        while(it.hasNext()) {
            if (!it.next().isTerm())
                return false;
        }
        
        return true;
    }
    
    public ListOfKeYJavaType getSignature(Services services) {
            
        ListOfKeYJavaType result = SLListOfKeYJavaType.EMPTY_LIST;
        IteratorOfSLExpression it = parameters.iterator();
        
        while(it.hasNext()) {
            result = result.append( it.next().getKeYJavaType(services.getJavaInfo()) );
        }
        
        return result;
    }
        

}
