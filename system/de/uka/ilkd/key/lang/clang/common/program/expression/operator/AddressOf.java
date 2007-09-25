package de.uka.ilkd.key.lang.clang.common.program.expression.operator;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.lang.clang.common.dispatch.IClangProgramDispatcher;
import de.uka.ilkd.key.lang.clang.common.iface.IClangEnvironment;
import de.uka.ilkd.key.lang.clang.common.program.expression.ClangExpressionUtil;
import de.uka.ilkd.key.lang.clang.common.program.iface.BaseClangExpression;
import de.uka.ilkd.key.lang.clang.common.program.iface.IClangExpression;
import de.uka.ilkd.key.lang.clang.common.type.IClangObjectType;
import de.uka.ilkd.key.lang.common.program.IProgramElement;
import de.uka.ilkd.key.lang.common.type.TypeErrorException;
import de.uka.ilkd.key.util.ExtList;

public final class AddressOf extends BaseClangExpression {
        public AddressOf(IClangExpression expression) {
                super(expression);
        }

        public AddressOf(ExtList children, AddressOf original) {
                super(children, original);
        }
        
        public IProgramElement copy(ExtList children) {
                return new AddressOf(children, this);
        }

        public void dispatch(IClangProgramDispatcher p) throws java.lang.Exception {
                p.dispatchAddressOf(this);
        }
        
        public Boolean isLvalue(IClangEnvironment environment) {
                return Boolean.FALSE;
        }

        public KeYJavaType getTypePair(IClangEnvironment environment) {
                Boolean isLvalue = ClangExpressionUtil.isLvalue(getExpressionAt(0), environment);
                if (isLvalue == Boolean.FALSE)
                        throw new TypeErrorException("Indirection must be applied to a lvalue", this);
                
                KeYJavaType typePair = ClangExpressionUtil.getTypePair(getExpressionAt(0), environment);
                if (typePair == null)
                        return null;
                
                if (!(typePair.getJavaType() instanceof IClangObjectType))
                        throw new TypeErrorException("Indirection applied to non-object type", this);
                
                return environment.getPlatform().getPointerTypePair(typePair);
        }
}
