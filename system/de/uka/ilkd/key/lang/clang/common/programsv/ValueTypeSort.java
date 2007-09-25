package de.uka.ilkd.key.lang.clang.common.programsv;

import de.uka.ilkd.key.lang.common.program.IProgramElement;
import de.uka.ilkd.key.lang.clang.common.iface.IClangEnvironment;
import de.uka.ilkd.key.lang.clang.common.program.iface.IClangTypeReference;
import de.uka.ilkd.key.lang.clang.common.type.IClangValueType;
import de.uka.ilkd.key.logic.Name;

/**
 * ProgramSV sort that matches on value type.
 * 
 * @author oleg.myrk@gmail.com
 */
public class ValueTypeSort extends BaseTypeProgramSVSort {

        public ValueTypeSort() {
                super(new Name("ClangValueType"));
        }

        protected boolean canStandFor(IProgramElement pe, IClangEnvironment context) {
                if (pe instanceof IClangTypeReference) {
                        IClangTypeReference typeReference = (IClangTypeReference) pe;
                        return (typeReference.getTypePair().getJavaType() instanceof IClangValueType);
                }
                return false;
        }
}