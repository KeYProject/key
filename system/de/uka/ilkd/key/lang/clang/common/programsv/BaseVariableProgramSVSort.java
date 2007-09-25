package de.uka.ilkd.key.lang.clang.common.programsv;

import de.uka.ilkd.key.lang.common.programsv.BaseProgramSV;
import de.uka.ilkd.key.lang.common.programsv.IVariableProgramSVSort;
import de.uka.ilkd.key.logic.Name;

public abstract class BaseVariableProgramSVSort extends BaseClangProgramSVSort implements
                IVariableSort, IVariableProgramSVSort {
        public BaseVariableProgramSVSort(Name name) {
                super(name);
        }

        public BaseProgramSV buildProgramSV(Name name) {
                return new VariableProgramSV(name, this);
        }
}
