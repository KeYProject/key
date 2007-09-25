package de.uka.ilkd.key.lang.clang.common.programsv;

import de.uka.ilkd.key.lang.clang.common.iface.IClangEnvironment;
import de.uka.ilkd.key.lang.clang.common.program.iface.IClangMemberReference;
import de.uka.ilkd.key.lang.common.program.IProgramElement;
import de.uka.ilkd.key.lang.common.programsv.BaseProgramSV;
import de.uka.ilkd.key.logic.Name;

/**
 * ProgramSV sort that matches on structured type members.
 * 
 * @author oleg.myrk@gmail.com
 */
public class MemberReferenceSort extends BaseClangProgramSVSort {

        public MemberReferenceSort() {
                super(new Name("ClangMember"));
        }

        protected boolean canStandFor(IProgramElement pe, IClangEnvironment context) {
                return pe instanceof IClangMemberReference;
        }

        public BaseProgramSV buildProgramSV(Name name) {
                return new MemberReferenceProgramSV(name, this);
        }
}