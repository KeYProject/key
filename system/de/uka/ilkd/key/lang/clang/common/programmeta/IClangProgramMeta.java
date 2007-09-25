package de.uka.ilkd.key.lang.clang.common.programmeta;

import de.uka.ilkd.key.lang.clang.common.iface.IClangEnvironment;
import de.uka.ilkd.key.lang.common.program.IProgramElement;
import de.uka.ilkd.key.lang.common.programmeta.IProgramMeta;
import de.uka.ilkd.key.lang.common.programsv.ArrayOfBaseProgramSV;
import de.uka.ilkd.key.logic.Named;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/**
 * An interface of C program meta constructions. Has a name and
 * a list of programSVs acting as arguments.
 * 
 * 
 * @author oleg.myrk@gmail.com
 *
 */
public interface IClangProgramMeta extends IProgramMeta, Named {
        /**
         * Returns an array of arguments.
         * @return
         */
        ArrayOfBaseProgramSV getArguments();

        /**
         * Executes the program meta contruction. SV instantiations
         * must contain instantiations of all arguments.
         * 
         * @param environment
         * @param svInsts
         * @return
         */
        IProgramElement execute(IClangEnvironment environment,
                        SVInstantiations svInsts);
}
