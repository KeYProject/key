package de.uka.ilkd.key.lang.clang.common.programsv;

import de.uka.ilkd.key.lang.common.programsv.BaseProgramSV;
import de.uka.ilkd.key.logic.Name;

public abstract class BaseTypeProgramSVSort extends BaseClangProgramSVSort implements
                ITypeSort {
        public BaseTypeProgramSVSort(Name name) {
                super(name);
        }

        public BaseProgramSV buildProgramSV(Name name) {
                return new TypeProgramSV(name, this);
        }
}
