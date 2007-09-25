package de.uka.ilkd.key.lang.clang.common.programsv;

import de.uka.ilkd.key.lang.common.program.IProgramElement;
import de.uka.ilkd.key.lang.clang.common.iface.IClangEnvironment;
import de.uka.ilkd.key.lang.clang.common.program.iface.IClangVariable;
import de.uka.ilkd.key.lang.clang.common.type.IClangObjectType;
import de.uka.ilkd.key.logic.Name;

/**
 * ProgramSV sort that matches on program variables of object type.
 * 
 * @author oleg.myrk@gmail.com
 */
public class ObjectVariableSort extends BaseVariableProgramSVSort {

        public ObjectVariableSort() {
                super(new Name("ClangObjectVariable"));
        }

        protected boolean canStandFor(IProgramElement pe, IClangEnvironment context) {
                if (pe instanceof IClangVariable) {
                        IClangVariable variable = (IClangVariable) pe;
                        return variable.getTypePair().getJavaType() instanceof IClangObjectType;
                }
                return false;
        }
}