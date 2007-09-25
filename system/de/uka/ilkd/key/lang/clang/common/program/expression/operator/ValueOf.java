package de.uka.ilkd.key.lang.clang.common.program.expression.operator;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.lang.clang.common.dispatch.IClangProgramDispatcher;
import de.uka.ilkd.key.lang.clang.common.iface.IClangEnvironment;
import de.uka.ilkd.key.lang.clang.common.program.expression.ClangExpressionUtil;
import de.uka.ilkd.key.lang.clang.common.program.expression.operator.arithmetic.Divide;
import de.uka.ilkd.key.lang.clang.common.program.iface.BaseClangExpression;
import de.uka.ilkd.key.lang.clang.common.program.iface.IClangExpression;
import de.uka.ilkd.key.lang.clang.common.sort.object.IScalarSort;
import de.uka.ilkd.key.lang.clang.common.type.object.ScalarType;
import de.uka.ilkd.key.lang.common.program.IProgramElement;
import de.uka.ilkd.key.lang.common.type.TypeErrorException;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.util.ExtList;

public final class ValueOf extends BaseClangExpression {
        public ValueOf(IClangExpression expr) {
                super(expr);
        }

        public ValueOf(ExtList children, ValueOf original) {
                super(children, original);
        }
        
        public IProgramElement copy(ExtList children) {
                return new ValueOf(children, this);
        }
        
        public void dispatch(IClangProgramDispatcher p) throws java.lang.Exception {
                p.dispatchValueOf(this);
        }

        public Boolean isLvalue(IClangEnvironment environment) {
                return ClangExpressionUtil.isLvalue(getExpressionAt(0), environment);
        }
        
        public KeYJavaType getTypePair(IClangEnvironment environment) {
                KeYJavaType typePair = ClangExpressionUtil.getTypePair(
                                getExpressionAt(0), environment);

                if (typePair == null)
                        return null;

                if (!(typePair.getJavaType() instanceof ScalarType))
                        throw new TypeErrorException(
                                        "ValueOf applied to non-scalar type",
                                        this);

                Type valueType = ((ScalarType) typePair.getJavaType())
                                .getValueType();
                Sort valueSort = ((IScalarSort) typePair.getSort())
                                .getValueSort();
                return new KeYJavaType(valueType, valueSort);
        }

}
