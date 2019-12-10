package de.uka.ilkd.key.nparser.varexp;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.op.ParsableVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.conditions.TypeResolver;

public enum ArgumentType {
    TYPE_RESOLVER(TypeResolver.class),
    SORT(Sort.class),
    JAVA_TYPE(KeYJavaType.class),
    VARIABLE(ParsableVariable.class),
    STRING(String.class);

    public final Class clazz;

    ArgumentType(Class<?> clazz) {
        this.clazz = clazz;
    }
}