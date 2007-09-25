package de.uka.ilkd.key.lang.clang.common.programsv;

import de.uka.ilkd.key.lang.clang.common.iface.IClangEnvironment;
import de.uka.ilkd.key.lang.clang.common.iface.IClangServices;
import de.uka.ilkd.key.lang.common.program.IProgramElement;
import de.uka.ilkd.key.lang.common.programsv.BaseProgramSVSort;
import de.uka.ilkd.key.lang.common.services.ILangServices;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Namespace;

/**
 * Base ProgramSV sort implementation for C language.
 * 
 * @author oleg.myrk@gmail.com
 */
public abstract class BaseClangProgramSVSort extends BaseProgramSVSort {
        public BaseClangProgramSVSort(Name name) {
                super(name);
        }

        /**
         * @inheritDocs
         */
        public final boolean canStandFor(IProgramElement pe,
                        ILangServices services, Namespace sortNS,
                        Namespace symbolNS) {
                return canStandFor(pe, ((IClangServices) services)
                                .getEnvironment(sortNS, symbolNS));

        }

        /**
         * Extend this method to define matching behavior.
         * 
         * @param pe
         * @param environment
         * @return
         */
        protected abstract boolean canStandFor(IProgramElement pe,
                        IClangEnvironment environment);
}
