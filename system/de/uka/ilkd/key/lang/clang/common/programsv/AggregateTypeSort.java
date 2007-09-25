package de.uka.ilkd.key.lang.clang.common.programsv;

import de.uka.ilkd.key.lang.common.program.IProgramElement;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.lang.clang.common.iface.IClangEnvironment;
import de.uka.ilkd.key.lang.clang.common.program.iface.IClangTypeReference;
import de.uka.ilkd.key.lang.clang.common.type.IClangObjectType;
import de.uka.ilkd.key.lang.clang.common.type.object.ScalarType;
import de.uka.ilkd.key.logic.Name;

/**
 * ProgramSV sort that matches on aggregate object type.
 * 
 * @author oleg.myrk@gmail.com
 */
public class AggregateTypeSort extends BaseTypeProgramSVSort {

        public AggregateTypeSort() {
                super(new Name("ClangAggregateType"));
        }

        protected boolean canStandFor(IProgramElement pe, IClangEnvironment context) {
                if (pe instanceof IClangTypeReference) {
                        IClangTypeReference typeReference = (IClangTypeReference) pe;
                        Type type = typeReference.getTypePair().getJavaType();
                        return (type instanceof IClangObjectType && !(type instanceof ScalarType));
                }
                return false;
        }
}