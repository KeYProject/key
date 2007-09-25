package de.uka.ilkd.key.lang.clang.common.type.value;

import de.uka.ilkd.key.lang.clang.common.type.BaseClangType;
import de.uka.ilkd.key.lang.clang.common.type.IClangObjectType;
import de.uka.ilkd.key.lang.clang.common.type.IClangValueType;
import de.uka.ilkd.key.logic.Name;

/**
 * C program pointer type.
 * 
 * @author oleg.myrk@gmail.com
 */
public class PointerType extends BaseClangType implements IClangValueType {
        /**
         * Target object type.
         */
        private final IClangObjectType targetType;
        
        /**
         * Creates pointer type for given target object type. 
         * @param targetType target object type to use
         */
        public PointerType(IClangObjectType targetType) {
                this.targetType = targetType;
        }
        
        /**
         * Returns target object type.
         * 
         * @return target object type
         */
        public IClangObjectType getTargetType() {
                return targetType;
        }
        
        public boolean equals(Object o) {
                if (o instanceof PointerType)
                        return this.targetType.equals(((PointerType)o).targetType);
                else
                        return false;
        }
        
        protected Name buildName() {        
                return new Name(targetType.getName() + "*");
        }
        
        protected int buildHashCode() {
                return 31*targetType.hashCode() + PointerType.class.hashCode();
        }
}



