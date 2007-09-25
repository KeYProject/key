package de.uka.ilkd.key.lang.clang.common.type.value;

import de.uka.ilkd.key.lang.clang.common.type.BaseClangType;
import de.uka.ilkd.key.lang.clang.common.type.IClangValueType;
import de.uka.ilkd.key.lang.clang.common.type.declaration.ArithmeticTypeDecl;
import de.uka.ilkd.key.logic.Name;

/**
 * C program arithmetic type.
 * 
 * @author oleg.myrk@gmail.com
 */
public class ArithmeticType extends BaseClangType implements IClangValueType {
        /**
         * Arithmetic type declaration to which this type refers.
         */
        private final ArithmeticTypeDecl typeDecl;
        
        /**
         * Creates arithmetic type for given arithmetic type declaration.
         * @param typeDecl arithmetic type declaration to use
         */
        public ArithmeticType(ArithmeticTypeDecl typeDecl) {
                this.typeDecl = typeDecl;
        }
                
        /**
         * Returns declaration of arithmetic type this type refers to.
         * @return declaration of arithmetic type this type refers to
         */
        public ArithmeticTypeDecl getDecl() {
                return typeDecl;
        }
        
        public boolean equals(Object o) {
                if (o instanceof ArithmeticType)
                        return this.typeDecl.equals(((ArithmeticType)o).typeDecl);
                else
                        return false;
        }
        
        protected Name buildName() {        
                return new Name(typeDecl.getId());
        }
        
        protected int buildHashCode() {
                return typeDecl.hashCode();
        }        
}
