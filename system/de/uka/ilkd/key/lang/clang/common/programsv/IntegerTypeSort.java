package de.uka.ilkd.key.lang.clang.common.programsv;

import de.uka.ilkd.key.lang.common.program.IProgramElement;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.lang.clang.common.iface.IClangEnvironment;
import de.uka.ilkd.key.lang.clang.common.program.iface.IClangTypeReference;
import de.uka.ilkd.key.lang.clang.common.type.declaration.IntegerTypeDecl;
import de.uka.ilkd.key.lang.clang.common.type.value.ArithmeticType;
import de.uka.ilkd.key.logic.Name;

/**
 * ProgramSV sort that matches on integer types.
 * 
 * @author oleg.myrk@gmail.com
 */
public class IntegerTypeSort extends BaseTypeProgramSVSort {

        public IntegerTypeSort() {
                super(new Name("ClangIntegerType"));
        }

        protected boolean canStandFor(IProgramElement pe, IClangEnvironment context) {
                if (pe instanceof IClangTypeReference) {
                        IClangTypeReference typeReference = (IClangTypeReference) pe;
                        Type type = typeReference.getTypePair().getJavaType();
                        if (type instanceof ArithmeticType)
                                return ((ArithmeticType)type).getDecl() instanceof IntegerTypeDecl;
                }
                return false;
        }
}