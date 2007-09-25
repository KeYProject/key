package de.uka.ilkd.key.lang.clang.common.type.object;

import de.uka.ilkd.key.lang.clang.common.type.BaseClangType;
import de.uka.ilkd.key.lang.clang.common.type.IClangInstantiableObjectType;
import de.uka.ilkd.key.lang.clang.common.type.IClangValueType;
import de.uka.ilkd.key.logic.Name;

/**
 * C program scalar object type.
 * 
 * @author oleg.myrk@gmail.com
 */
public class ScalarType extends BaseClangType implements IClangInstantiableObjectType {
        /**
         * Target type.
         */
        private final IClangValueType valueType;        
        
        /**
         * Creates scalar type for given value type.
         * @param valueType value type to use
         */
        public ScalarType(IClangValueType valueType) {
                super();
                this.valueType = valueType;
        }
        
        /**
         * Returns value type.
         * 
         * @return value type
         */
        public IClangValueType getValueType() {
                return valueType;
        }
        
        public boolean equals(Object o) {
                if (o instanceof ScalarType)
                        return 
                                this.valueType.equals(((ScalarType)o).valueType);
                else
                        return false;
        }

        protected Name buildName() {        
                return new Name(valueType.getName() + "@");
        }
        
        protected int buildHashCode() {
                return 31*valueType.hashCode() + ScalarType.class.hashCode();
        }
}
