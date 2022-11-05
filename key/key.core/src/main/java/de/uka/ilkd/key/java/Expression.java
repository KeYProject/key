package de.uka.ilkd.key.java;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.reference.ExecutionContext;


/**
 * Expression taken from COMPOST and changed to achieve an immutable structure
 */
public interface Expression extends ProgramElement {

    /**
     * returns the {@link KeYJavaType} of an expression
     */
    KeYJavaType getKeYJavaType(Services javaServ, ExecutionContext ec);
}
