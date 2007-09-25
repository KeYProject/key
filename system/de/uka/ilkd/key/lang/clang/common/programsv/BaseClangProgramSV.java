package de.uka.ilkd.key.lang.clang.common.programsv;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.lang.clang.common.dispatch.IClangDispatchableProgramElement;
import de.uka.ilkd.key.lang.clang.common.dispatch.IClangProgramDispatcher;
import de.uka.ilkd.key.lang.clang.common.pprinter.ClangProgramPrinter;
import de.uka.ilkd.key.lang.common.pprinter.IProgramPrinter;
import de.uka.ilkd.key.lang.common.programsv.BaseProgramSV;
import de.uka.ilkd.key.lang.common.programsv.BaseProgramSVSort;
import de.uka.ilkd.key.lang.common.services.ILangServices;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Namespace;

/**
 * Base implementation of C programSV. Subclasses will introduce additional
 * interfaces needed to fit into the AST at specific places.
 * 
 * @author oleg.myrk@gmail.com
 */
public abstract class BaseClangProgramSV extends BaseProgramSV implements IClangDispatchableProgramElement {
        public BaseClangProgramSV(Name name, BaseProgramSVSort s) {
                super(name, s);
        }

        /**
         * @inhertidDocs
         */
        public IProgramPrinter createDefaultPrinter() {
                return new ClangProgramPrinter();
        }
        
        /**
         * @inhertidDocs
         */
        public void dispatch(IClangProgramDispatcher p) throws Exception {
                p.dispatchProgramSV(this);
        }
        
        /**
         * @inhertidDocs
         */
        public KeYJavaType getTypePair(ILangServices services, Namespace sortNS, Namespace funcctionNS) {
                throw new IllegalStateException("ExpressionProgramSV does not have a type!");
        }        
}