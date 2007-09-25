package de.uka.ilkd.key.lang.clang.common.program.expression.operator.arithmetic;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.lang.clang.common.dispatch.IClangProgramDispatcher;
import de.uka.ilkd.key.lang.clang.common.iface.IClangEnvironment;
import de.uka.ilkd.key.lang.clang.common.program.expression.ClangExpressionUtil;
import de.uka.ilkd.key.lang.clang.common.program.expression.operator.ArithmeticUtils;
import de.uka.ilkd.key.lang.clang.common.program.iface.BaseClangExpression;
import de.uka.ilkd.key.lang.clang.common.program.iface.IClangExpression;
import de.uka.ilkd.key.lang.clang.common.sort.object.IScalarSort;
import de.uka.ilkd.key.lang.clang.common.type.object.ScalarType;
import de.uka.ilkd.key.lang.clang.common.type.value.PointerType;
import de.uka.ilkd.key.lang.common.program.IProgramElement;
import de.uka.ilkd.key.lang.common.type.TypeErrorException;
import de.uka.ilkd.key.util.ExtList;

public final class IncrementPrefix extends BaseClangExpression {
        
        public IncrementPrefix(IClangExpression expression) {
                super(expression);
        }

        public IncrementPrefix(ExtList children, IncrementPrefix original) {
                super(children, original);
        }
        
        public IProgramElement copy(ExtList children) {
                return new IncrementPrefix(children, this);
        }
        
        public void dispatch(IClangProgramDispatcher p) throws java.lang.Exception {
                p.dispatchIncrementPrefix(this);
        }
        
        public Boolean isLvalue(IClangEnvironment environment) {
                return Boolean.FALSE;
        }
        
        public KeYJavaType getTypePair(IClangEnvironment environment) {
                Boolean isLvalue = ClangExpressionUtil.isLvalue(getExpressionAt(0), environment);
                if (isLvalue == Boolean.FALSE)
                        throw new TypeErrorException("IncrementPrefix must be applied to a lvalue", this);
                
                KeYJavaType typePair = ClangExpressionUtil.getTypePair(getExpressionAt(0), environment);
                if (typePair == null)
                        return null;
                
                if (typePair.getJavaType() instanceof ScalarType)
                        typePair = new KeYJavaType(
                                        ((ScalarType)typePair.getJavaType()).getValueType(),
                                        ((IScalarSort)typePair.getSort()).getValueSort()
                                        );                                        
                
                if (!(ArithmeticUtils.isNonPromotableType(typePair.getJavaType()) ||
                                typePair.getJavaType() instanceof PointerType))
                        throw new TypeErrorException("IncrementPrefix applied to incompatible type (no promotions)", this);
                
                return typePair;
        }
}
