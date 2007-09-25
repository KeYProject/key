package de.uka.ilkd.key.lang.common.programsv;

import java.io.IOException;
import java.util.Set;

import de.uka.ilkd.key.java.NameAbstractionTable;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.lang.common.pprinter.ProgramPrinterUtil;
import de.uka.ilkd.key.lang.common.program.IProgramElement;
import de.uka.ilkd.key.lang.common.program.ISchemaProgramElement;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.op.ProgramSV;
import de.uka.ilkd.key.util.Debug;

/**
 * A schema program element that is also a schema variable. It matches
 * program elements determined by its sort {@link BaseProgramSVSort}.
 * Subclasses will typically add more program element interfaces 
 * to this class to make sure it fits in into the required parts 
 * of the AST.
 * 
 * @author oleg.myrk@gmail.com
 */
public abstract class BaseProgramSV extends ProgramSV implements
                ISchemaProgramElement {
        
        public BaseProgramSV(Name name, BaseProgramSVSort s) {
                super(name, s, false);
        }
        
        /**
         * Returns the sort of this programSV.
         * @return
         */
        public BaseProgramSVSort programSVSort() {
                return (BaseProgramSVSort)sort();
        }

        /**
         * @inheritDocs
         */
        public final boolean equalsModRenaming(IProgramElement programElement,
                        NameAbstractionTable nat) {
                return programElement == this;
        }
        
        /**
         * @inheritDocs
         */
        public final Set getAllVariables() {
                throw new IllegalStateException("BaseProgramSV.getAllVariables() should not be called!");
        }
        
        /**
         * @inheritDocs
         */
        public final String toString() {
                return toString("program "+sort().name());
        }        
        
        /**
         * @deprecated
         */
        public final boolean equalsModRenaming(SourceElement se,
                        NameAbstractionTable nat) {
                return equalsModRenaming(se, nat);
        }        
}
