package de.uka.ilkd.key.lang.clang.common.type;

import de.uka.ilkd.key.lang.common.type.BaseType;
import de.uka.ilkd.key.logic.Name;

/**
 * Abstract base implementation of C program types.
 * 
 * We extend base Java program {@link de.uka.ilkd.key.java.abstraction.Type}
 * because everything depends on it through 
 * {@link de.uka.ilkd.key.logic.op.ProgramVariable} and
 * {@link de.uka.ilkd.key.java.abstraction.KeyJavaType}.
 * 
 * @author oleg.myrk@gmail.com
 */
public abstract class BaseClangType extends BaseType implements IClangType {
        private boolean nameBuilt = false;
        private Name name;
        private boolean hashCodeBuilt = false; 
        private int hashCode;
        
        public Name name() {
                if (!nameBuilt) {
                        name = buildName();
                        nameBuilt = true;
                }
                return name;
        }
        
        public abstract boolean equals(Object o);
        
        public int hashCode() {
                if (!hashCodeBuilt) {
                        hashCode = buildHashCode();
                        hashCodeBuilt = true;
                }
                return hashCode;
        }
        
        public String toString() {
                return name().toString();
        }

        /**
         * Builds the name of the type (will be cached).
         * @return
         */
        protected abstract Name buildName();
        
        /**
         * Builds the name of the type (will be cached).
         * @return
         */
        protected abstract int buildHashCode();
}