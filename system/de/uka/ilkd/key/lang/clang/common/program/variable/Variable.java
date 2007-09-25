package de.uka.ilkd.key.lang.clang.common.program.variable;

import de.uka.ilkd.key.java.NameAbstractionTable;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.lang.clang.common.dispatch.IClangProgramDispatcher;
import de.uka.ilkd.key.lang.clang.common.iface.IClangEnvironment;
import de.uka.ilkd.key.lang.clang.common.program.iface.BaseClangVariable;
import de.uka.ilkd.key.lang.common.program.IProgramElement;
import de.uka.ilkd.key.logic.Name;

/**
 * Program variable.
 * @author oleg.myrk@gmail.com
 */
public class Variable extends BaseClangVariable {
        public Variable(Name name, KeYJavaType t) {
                super(name, t);
        }
        
        public Boolean isLvalue(IClangEnvironment environment) {
                return Boolean.TRUE;
        }

        public void dispatch(IClangProgramDispatcher p) throws java.lang.Exception {
                p.dispatchVariable(this);
        }       
        
        public boolean equalsModRenaming(IProgramElement pe, 
                             NameAbstractionTable nat) {
                return nat.sameAbstractName(this, pe);
        }        
}
