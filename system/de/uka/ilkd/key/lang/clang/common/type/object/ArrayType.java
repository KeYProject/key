package de.uka.ilkd.key.lang.clang.common.type.object;

import java.math.BigInteger;

import de.uka.ilkd.key.lang.clang.common.type.BaseClangType;
import de.uka.ilkd.key.lang.clang.common.type.IClangInstantiableObjectType;
import de.uka.ilkd.key.logic.Name;

/**
 * C program array object type.
 * 
 * @author oleg.myrk@gmail.com
 */
public class ArrayType extends BaseClangType implements IClangInstantiableObjectType {
        /**
         * Element object type.
         */
        private final IClangInstantiableObjectType elemType;
        
        /**
         * Array size.
         */
        private final BigInteger size;
        
        /**
         * Creates array object type for given element object type. 
         * @param elementType element object type.
         * @param size array size
         */
        public ArrayType(IClangInstantiableObjectType elemType, BigInteger size) {
                this.elemType = elemType;
                this.size = size;
        }
        
        /**
         * Returns element type.
         * 
         * @return element type
         */
        public IClangInstantiableObjectType getElemType() {
                return elemType;
        }
        
        /**
         * Returns the array size.
         * 
         * @return array size
         */
        public BigInteger getSize() {
                return size;
        }
        
        public boolean equals(Object o) {
                if (o instanceof ArrayType)
                        return  
                                this.elemType.equals(((ArrayType)o).elemType) &&
                                this.size.equals(((ArrayType)o).size);
                else
                        return false;
        }

        protected Name buildName() {
                return new Name(elemType.getName() + "[" + size.toString() + "]");
        }
        
        protected int buildHashCode() {
                return elemType.hashCode()*31 + size.hashCode();
        }        
        
}
