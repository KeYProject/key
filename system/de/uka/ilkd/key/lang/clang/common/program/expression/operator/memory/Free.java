package de.uka.ilkd.key.lang.clang.common.program.expression.operator.memory;

import java.lang.Exception;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.lang.clang.common.dispatch.IClangProgramDispatcher;
import de.uka.ilkd.key.lang.clang.common.iface.IClangEnvironment;
import de.uka.ilkd.key.lang.clang.common.program.expression.ClangExpressionUtil;
import de.uka.ilkd.key.lang.clang.common.program.expression.operator.arithmetic.Divide;
import de.uka.ilkd.key.lang.clang.common.program.iface.BaseClangExpression;
import de.uka.ilkd.key.lang.clang.common.program.iface.IClangExpression;
import de.uka.ilkd.key.lang.clang.common.type.value.PointerType;
import de.uka.ilkd.key.lang.common.program.IProgramElement;
import de.uka.ilkd.key.lang.common.type.TypeErrorException;
import de.uka.ilkd.key.util.ExtList;

public final class Free extends BaseClangExpression {

        private KeYJavaType resultTypePair;
        
        public Free(IClangExpression child, KeYJavaType resultTypePair) {
                super(child);
                this.resultTypePair = resultTypePair;
        }

        public Free(ExtList children, Free original) {
                super(children, original);
                this.resultTypePair = original.resultTypePair;
        }
        
        public IProgramElement copy(ExtList children) {
                return new Free(children, this);
        }
        
        public void dispatch(IClangProgramDispatcher w) throws Exception {
                w.dispatchFree(this);
        }
        
        public Boolean isLvalue(IClangEnvironment environment) {
                return Boolean.FALSE;
        }
        
        public KeYJavaType getTypePair(IClangEnvironment environment) {
                KeYJavaType typePair = ClangExpressionUtil.getTypePair(getExpressionAt(0), environment);
                if (typePair == null)
                        return null;
                
                if (!(typePair.getJavaType() instanceof PointerType))
                        throw new TypeErrorException("Free applied to non-pointer type", this);
                
                
                return resultTypePair;
        }

}
