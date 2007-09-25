package de.uka.ilkd.key.lang.clang.common.programsv;

import de.uka.ilkd.key.lang.common.program.IProgramElement;
import de.uka.ilkd.key.lang.clang.common.iface.IClangEnvironment;
import de.uka.ilkd.key.lang.clang.common.program.iface.IClangTypeReference;
import de.uka.ilkd.key.lang.clang.common.type.IClangObjectType;
import de.uka.ilkd.key.logic.Name;

/**
 * ProgramSV sort that matches on object type.
 * 
 * @author oleg.myrk@gmail.com
 */
public class ObjectTypeSort extends BaseTypeProgramSVSort {

        public ObjectTypeSort() {
                super(new Name("ClangObjectType"));
        }

        protected boolean canStandFor(IProgramElement pe, IClangEnvironment context) {
                if (pe instanceof IClangTypeReference) {
                        IClangTypeReference typeReference = (IClangTypeReference) pe;
                        return (typeReference.getTypePair().getJavaType() instanceof IClangObjectType);
                }
                return false;
        }
}