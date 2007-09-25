package de.uka.ilkd.key.lang.clang.common.programsv;

import de.uka.ilkd.key.lang.clang.common.program.iface.IClangStatement;
import de.uka.ilkd.key.lang.common.programsv.BaseProgramSVSort;
import de.uka.ilkd.key.logic.Name;

public class StatementProgramSV extends BaseClangProgramSV implements IClangStatement {
        public StatementProgramSV(Name name, BaseProgramSVSort s) {
                super(name, s);
        }
}
