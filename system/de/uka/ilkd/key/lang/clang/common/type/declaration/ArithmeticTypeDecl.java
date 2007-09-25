package de.uka.ilkd.key.lang.clang.common.type.declaration;


/**
 * C program arithmetic type declaration.
 * 
 * @author oleg.myrk@gmail.com
 */
public class ArithmeticTypeDecl  {
        /**
         * Identifier of this type
         */
        private final String id;
        
        /**
         * Creates arithmetic type declaration with given identifier.
         * @param id identifier to use
         */
        public ArithmeticTypeDecl(String id) {
                this.id = id;
        }
        
        /**
         * Returns id of the arithmetic type.
         * @return id
         */
        public String getId() {
                return id;
        }
}
