package de.uka.ilkd.key.lang.clang.common.programsv;

import de.uka.ilkd.key.lang.common.program.IProgramElement;
import de.uka.ilkd.key.lang.clang.common.iface.IClangEnvironment;
import de.uka.ilkd.key.lang.clang.common.program.iface.IClangTypeReference;
import de.uka.ilkd.key.lang.clang.common.type.object.ScalarType;
import de.uka.ilkd.key.logic.Name;

/**
 * ProgramSV sort that matches on scalar object type.
 * 
 * @author oleg.myrk@gmail.com
 */
public class ScalarTypeSort extends BaseTypeProgramSVSort {

        public ScalarTypeSort() {
                super(new Name("ClangScalarType"));
        }

        protected boolean canStandFor(IProgramElement pe, IClangEnvironment context) {
                if (pe instanceof IClangTypeReference) {
                        IClangTypeReference typeReference = (IClangTypeReference) pe;
                        return (typeReference.getTypePair().getJavaType() instanceof ScalarType);
                }
                return false;
        }
}