package de.uka.ilkd.key.lang.common.type;

import de.uka.ilkd.key.logic.Named;

/**
 * Represents a program type.
 * 
 * @author oleg.myrk@gmail.com
 */
public interface IType extends de.uka.ilkd.key.java.abstraction.Type, Named {       
        /**
         * Tests objects for equality. Type objects are equal when they 
         * represent the same C program type.
         */
        boolean equals(Object o);
        
        /**
         * Computes object's hash code. Should comply with the equals method.
         * @return
         */
        int hashCode();
}
