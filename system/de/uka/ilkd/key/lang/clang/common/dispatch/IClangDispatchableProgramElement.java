package de.uka.ilkd.key.lang.clang.common.dispatch;

import de.uka.ilkd.key.lang.common.program.IProgramElement;

/**
 * A C program element that supports double dispatch pattern.
 *  
 * @author oleg.myrk@gmail.com
 */
public interface IClangDispatchableProgramElement extends IProgramElement {
        public void dispatch(IClangProgramDispatcher programElement) throws Exception;
}
