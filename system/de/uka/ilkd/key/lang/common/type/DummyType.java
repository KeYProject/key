package de.uka.ilkd.key.lang.common.type;

import de.uka.ilkd.key.java.expression.Literal;

/**
 * An implementation of program type's legacy methods.
 * 
 * @author oleg.myrk@gmail.com
 */
public abstract class DummyType implements IType {
        
        /**
         * @deprecated
         */
        final public String getName() {
                return name().toString();
        }

        /**
         * @deprecated
         */
        final public String getFullName() {
                return name().toString();
        }

        /**
         * @deprecated
         */
        final public Literal getDefaultValue() {
                return null;
        }
}