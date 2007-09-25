package de.uka.ilkd.key.lang.clang.common.type.object;

import de.uka.ilkd.key.lang.clang.common.type.BaseClangType;
import de.uka.ilkd.key.lang.clang.common.type.IClangInstantiableObjectType;
import de.uka.ilkd.key.lang.clang.common.type.declaration.StructDecl;
import de.uka.ilkd.key.logic.Name;

/**
 * C program struct object type.
 * 
 * @author oleg.myrk@gmail.com
 */
public class StructType extends BaseClangType implements IClangInstantiableObjectType {
        /**
         * Struct declaration to which this type refers.
         */
        final private StructDecl typeDecl;
        
        /**
         * Creates struct type for given struct declaration. 
         * @param typeDecl struct declaration to which this type refers.
         */
        public StructType(StructDecl typeDecl) {
                this.typeDecl = typeDecl;
        }
        
        /**
         * Returns struct declaration to which this type refers.
         * @return struct declaratoin to which this type refers.
         */
        public StructDecl getDecl() {
                return typeDecl;
        }
        
        public boolean equals(Object o) {
                if (o instanceof StructType)
                        return this.typeDecl.equals(((StructType)o).typeDecl);
                else
                        return false;
        }

        protected Name buildName() {        
                return new Name("struct " + typeDecl.getId());
        }
        
        protected int buildHashCode() {
                return typeDecl.hashCode();
        }               
        
}
