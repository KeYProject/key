package de.uka.ilkd.key.lang.clang.common.type.object;

import de.uka.ilkd.key.lang.clang.common.type.BaseClangType;
import de.uka.ilkd.key.lang.clang.common.type.IClangObjectType;
import de.uka.ilkd.key.logic.Name;

/**
 * C program void object type.
 * 
 * @author oleg.myrk@gmail.com
 */
public class VoidType extends BaseClangType implements IClangObjectType {       
        /**
         * Creates void type. 
         */
        public VoidType() {
        }
        
        public boolean equals(Object o) {
                return (o instanceof VoidType);
        }

        protected Name buildName() {        
                return new Name("void");
        }
        
        protected int buildHashCode() {
                return VoidType.class.hashCode();
        }               
}
