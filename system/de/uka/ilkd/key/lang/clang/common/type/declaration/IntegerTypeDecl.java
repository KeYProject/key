package de.uka.ilkd.key.lang.clang.common.type.declaration;


/**
 * C program arithmetic integer type declaration.
 * 
 * @author oleg.myrk@gmail.com
 */
public class IntegerTypeDecl extends ArithmeticTypeDecl {
        /**
         * Whether this type has to be promoted when used in arithmetic expressions.
         */
        private final boolean needsPromotion;
        
        /**
         * Creates arithmetic integer type declaration with given identifier.
         * @param id identifier to use
         * @param needsPromotion whether this type has to be promoted when used in arithmetic expressions
         */
        public IntegerTypeDecl(String id, boolean needsPromotion) {
                super(id);
                this.needsPromotion = needsPromotion;
        }
        
        /**
         * Whether this type has to be promoted when used in arithmetic expressions.
         * @return
         */
        public boolean needsPromotion() {
                return needsPromotion;
        }
}
