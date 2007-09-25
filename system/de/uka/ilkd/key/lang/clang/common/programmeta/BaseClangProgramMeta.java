package de.uka.ilkd.key.lang.clang.common.programmeta;

import de.uka.ilkd.key.lang.clang.common.dispatch.IClangDispatchableProgramElement;
import de.uka.ilkd.key.lang.clang.common.dispatch.IClangProgramDispatcher;
import de.uka.ilkd.key.lang.clang.common.pprinter.ClangProgramPrinter;
import de.uka.ilkd.key.lang.common.pprinter.IProgramPrinter;
import de.uka.ilkd.key.lang.common.program.IProgramElement;
import de.uka.ilkd.key.lang.common.programmeta.BaseProgramMeta;
import de.uka.ilkd.key.lang.common.programsv.ArrayOfBaseProgramSV;
import de.uka.ilkd.key.logic.Name;

/**
 * Base program meta construct implementation for C language.
 * 
 * @author oleg.myrk@gmail.com
 */
public abstract class BaseClangProgramMeta extends BaseProgramMeta implements
                IClangProgramMeta, IClangDispatchableProgramElement {
        private final Name name;
        private final ArrayOfBaseProgramSV arguments;
        
        public BaseClangProgramMeta(Name name, ArrayOfBaseProgramSV arguments) {
                this.name = name;
                this.arguments = arguments;
        }
        
        /**
         * @inheritDocs
         */
        public final Name name() {
                return name;
        }

        /**
         * @inheritDocs
         */
        public final ArrayOfBaseProgramSV getArguments() {
                return arguments;
        }

        /**
         * Checks if the argument has given number of arguments. Reports error, if not.
         * @param count
         */
        protected final void checkArgumentCount(int count) {
                if (count != arguments.size())
                        if (getArguments().size() != 1)
                                reportError(name()
                                                + " should be applied to exactly one argument");

        }

        /**
         * Reports error message.
         * @param message
         * @throw IllegalArgumentException
         */
        protected final void reportError(String message) {
                throw new IllegalArgumentException(message);
        }

        /**
         * @inheritDocs
         */
        public IProgramPrinter createDefaultPrinter() {
                return new ClangProgramPrinter();
        }

        /**
         * @inheritDocs
         */
        public void dispatch(IClangProgramDispatcher p) throws Exception {
                p.dispatchProgramMeta(this);
        }
}
