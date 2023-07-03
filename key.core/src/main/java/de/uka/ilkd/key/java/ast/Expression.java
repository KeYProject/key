package de.uka.ilkd.key.java.ast;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.ast.reference.ExecutionContext;


/**
 * Expression taken from COMPOST and changed to achieve an immutable structure
 */
public interface Expression extends ProgramElement {
    /**
     * returns the {@link KeYJavaType} of an expression
     */
    KeYJavaType getKeYJavaType(Services javaServ, ExecutionContext ec);
}
