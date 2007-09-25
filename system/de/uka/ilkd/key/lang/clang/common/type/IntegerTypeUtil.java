package de.uka.ilkd.key.lang.clang.common.type;

import de.uka.ilkd.key.lang.clang.common.type.declaration.IntegerTypeDecl;

/**
 * Standard C type IDs.
 * 
 * @author oleg.myrk@gmail.com
 */
public class IntegerTypeUtil {
        public final static String CHAR_TYPE_ID = "char";
        public final static String SCHAR_TYPE_ID = "signed char";
        public final static String UCHAR_TYPE_ID = "unsigned char";
        public final static String SSHRT_TYPE_ID = "short";
        public final static String USHRT_TYPE_ID = "unsigned short";
        public final static String SINT_TYPE_ID = "int";
        public final static String UINT_TYPE_ID = "unsigned int";
        public final static String SLONG_TYPE_ID = "long";
        public final static String ULONG_TYPE_ID = "unsigned long";    
        public final static String SLLONG_TYPE_ID = "long long";
        public final static String ULLONG_TYPE_ID = "unsigned long long";

        /**
         * Registers standard C types in the type builder.
         */
        public static void registerStandardTypeDecls(TypeBuilder builder) {
                builder.addArithmeticTypeDecl(new IntegerTypeDecl(CHAR_TYPE_ID, true));
                builder.addArithmeticTypeDecl(new IntegerTypeDecl(SCHAR_TYPE_ID, true));
                builder.addArithmeticTypeDecl(new IntegerTypeDecl(UCHAR_TYPE_ID, true));
                builder.addArithmeticTypeDecl(new IntegerTypeDecl(SSHRT_TYPE_ID, true));
                builder.addArithmeticTypeDecl(new IntegerTypeDecl(USHRT_TYPE_ID, true));
                builder.addArithmeticTypeDecl(new IntegerTypeDecl(SINT_TYPE_ID, false));
                builder.addArithmeticTypeDecl(new IntegerTypeDecl(UINT_TYPE_ID, false));
                builder.addArithmeticTypeDecl(new IntegerTypeDecl(SLONG_TYPE_ID, false));
                builder.addArithmeticTypeDecl(new IntegerTypeDecl(ULONG_TYPE_ID, false));                
                builder.addArithmeticTypeDecl(new IntegerTypeDecl(SLLONG_TYPE_ID, false));
                builder.addArithmeticTypeDecl(new IntegerTypeDecl(ULLONG_TYPE_ID, false));                
        }
}
