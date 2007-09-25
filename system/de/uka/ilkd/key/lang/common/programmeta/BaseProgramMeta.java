package de.uka.ilkd.key.lang.common.programmeta;

import java.util.Set;

import de.uka.ilkd.key.java.NameAbstractionTable;
import de.uka.ilkd.key.java.SourceData;
import de.uka.ilkd.key.lang.common.program.DummyProgramElement;
import de.uka.ilkd.key.lang.common.program.IProgramElement;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.util.ExtList;

/**
 * Base program meta construct implementation.
 * 
 * @author oleg.myrk@gmail.com
 */
public abstract class BaseProgramMeta extends DummyProgramElement implements IProgramMeta {
        public IProgramElement copy(ExtList children) {
                throw new IllegalStateException("BaseProgramMeta.copy() should not be called!");
        }

        public final Set getAllVariables() {
                throw new IllegalStateException("BaseProgramMeta.getAllVariables() should not be called!");
        }

        public final boolean equalsModRenaming(IProgramElement se,
                        NameAbstractionTable nat) {
                throw new IllegalStateException("BaseProgramMeta.equalsModRenaming() should not be called!");
        }
        
        public MatchConditions match(SourceData source,
                        MatchConditions matchCond) {
                throw new IllegalStateException("BaseProgramMeta.match() should not be called!");        
        }        
}
