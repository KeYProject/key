package de.uka.ilkd.key.lang.common.programsv;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.lang.common.program.IProgramElement;
import de.uka.ilkd.key.lang.common.services.ILangServices;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.ProgramSV;
import de.uka.ilkd.key.logic.sort.ProgramSVSort;

/**
 * Base programSV sort implementation that determines which program
 * elements are matched by the programSV and allows creating programSVs
 * of this sort.
 * 
 * @author oleg.myrk@gmail.com
 */
public abstract class BaseProgramSVSort extends ProgramSVSort {
        public BaseProgramSVSort(Name name) {
                super(name);
        }

        /**
         * Tells if the program element is matched by programSVs of this sort.
         * 
         * @param pe
         * @param services
         * @param sortNS
         * @param symbolNS
         * @return
         */
        public abstract boolean canStandFor(IProgramElement pe, ILangServices services, Namespace sortNS, Namespace symbolNS);

        /**
         * Builds a programSV of this sort with given name.
         * @param name
         * @return
         */
        public abstract BaseProgramSV buildProgramSV(Name name);

        /**
         * @deprecated
         */
        public final boolean canStandFor(Term t) {
                return false;
        }

        /**
         * @deprecated
         */
        protected final boolean canStandFor(ProgramElement pe, Services services) {
                return pe instanceof IProgramElement && canStandFor((IProgramElement)pe, services.getLangServices(), services.getNamespaces().sorts(), services.getNamespaces().functions());
        }

        /**
         * @deprecated
         */
        public final ProgramSV createProgramSV(Name name, boolean listSV) {
                if (listSV)
                        throw new IllegalArgumentException("List ProgramSVs not supported");
                return buildProgramSV(name);
        }
}
