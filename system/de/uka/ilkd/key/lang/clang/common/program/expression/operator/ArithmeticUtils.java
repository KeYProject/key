package de.uka.ilkd.key.lang.clang.common.program.expression.operator;

import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.lang.clang.common.type.declaration.ArithmeticTypeDecl;
import de.uka.ilkd.key.lang.clang.common.type.declaration.IntegerTypeDecl;
import de.uka.ilkd.key.lang.clang.common.type.value.ArithmeticType;

public class ArithmeticUtils {
        /**
         * Tells if given program type is an arithmetic type that does not need promotion.
         * @param type
         * @return
         */
        public static boolean isNonPromotableType(Type type) {
                if (!(type instanceof ArithmeticType))
                        return false;
                ArithmeticTypeDecl decl = ((ArithmeticType)type).getDecl();
                if (!(decl instanceof IntegerTypeDecl)) 
                        return true;
                else
                        return !(((IntegerTypeDecl)decl).needsPromotion());                
        }
        
        /**
         * Tells if given program type is an integer type that does not need promotion.
         * @param type
         * @return
         */
        public static boolean isNonPromotableIntegerType(Type type) {
                if (!(type instanceof ArithmeticType))
                        return false;
                ArithmeticTypeDecl decl = ((ArithmeticType)type).getDecl();                
                return decl instanceof IntegerTypeDecl && 
                      !(((IntegerTypeDecl)decl).needsPromotion());
        }
        
        /**
         * Tells if given program type is an integer type.
         * @param type
         * @return
         */
        public static boolean isIntegerType(Type type) {
                if (!(type instanceof ArithmeticType))
                        return false;
                ArithmeticTypeDecl decl = ((ArithmeticType)type).getDecl();                
                return decl instanceof IntegerTypeDecl;
        }        
}
