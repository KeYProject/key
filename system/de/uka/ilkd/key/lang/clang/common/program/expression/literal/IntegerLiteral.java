package de.uka.ilkd.key.lang.clang.common.program.expression.literal;

import java.math.BigInteger;

import de.uka.ilkd.key.java.NameAbstractionTable;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.lang.clang.common.dispatch.IClangProgramDispatcher;
import de.uka.ilkd.key.lang.clang.common.iface.IClangEnvironment;
import de.uka.ilkd.key.lang.clang.common.program.iface.BaseClangLiteral;
import de.uka.ilkd.key.lang.common.program.IProgramElement;

public class IntegerLiteral extends BaseClangLiteral {

        private final BigInteger value;

        private final KeYJavaType type;

        public IntegerLiteral(BigInteger value, KeYJavaType type) {
                this.value = value;
                this.type = type;
        }
        
        public BigInteger getValue() {
                return value;
        }
        
        public KeYJavaType getType() {
                return type;
        }

        public boolean equalsModRenaming(IProgramElement pe,
                        NameAbstractionTable nat) {
                if (!super.equalsModRenaming(pe,nat))
                        return false;
                return ((IntegerLiteral) pe).getValue().equals(getValue());
        }

        public int hashCode() {
                int result = 17;
                result = 37 * result + getValue().hashCode();
                return result;
        }

        public void dispatch(IClangProgramDispatcher p) throws java.lang.Exception {
                p.dispatchIntLiteral(this);
        }
        
        public Boolean isLvalue(IClangEnvironment environment) {
                return Boolean.FALSE;
        }
                
        public KeYJavaType getTypePair(IClangEnvironment environment) {
                return type;
        }
}
