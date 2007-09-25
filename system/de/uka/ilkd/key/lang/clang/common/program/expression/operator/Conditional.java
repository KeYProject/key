package de.uka.ilkd.key.lang.clang.common.program.expression.operator;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.lang.clang.common.dispatch.IClangProgramDispatcher;
import de.uka.ilkd.key.lang.clang.common.iface.IClangEnvironment;
import de.uka.ilkd.key.lang.clang.common.program.expression.ClangExpressionUtil;
import de.uka.ilkd.key.lang.clang.common.program.iface.BaseClangExpression;
import de.uka.ilkd.key.lang.clang.common.program.iface.IClangExpression;
import de.uka.ilkd.key.lang.clang.common.program.statement.BlockFrame;
import de.uka.ilkd.key.lang.clang.common.type.IClangValueType;
import de.uka.ilkd.key.lang.clang.common.type.object.StructType;
import de.uka.ilkd.key.lang.common.program.IProgramElement;
import de.uka.ilkd.key.lang.common.type.TypeErrorException;
import de.uka.ilkd.key.util.ExtList;

public final class Conditional extends BaseClangExpression {
        public Conditional(ExtList children, Conditional original) {
                super(children, original);
        }
        
        public IProgramElement copy(ExtList children) {
                return new Conditional(children, this);
        }
        
        public Conditional(IClangExpression exp0, IClangExpression exp1, IClangExpression exp2) {
                super(new IClangExpression[] {exp0, exp1, exp2});
        }

        public void dispatch(IClangProgramDispatcher p) throws java.lang.Exception {
                p.dispatchConditional(this);
        }
        
        public Boolean isLvalue(IClangEnvironment environment) {
                return Boolean.FALSE;
        }
        
        public KeYJavaType getTypePair(IClangEnvironment environment) {

                KeYJavaType typePair0 = ClangExpressionUtil.getTypePair(
                                getExpressionAt(0), environment);
                KeYJavaType typePair1 = ClangExpressionUtil.getTypePair(
                                getExpressionAt(0), environment);
                KeYJavaType typePair2 = ClangExpressionUtil.getTypePair(
                                getExpressionAt(1), environment);

                if (typePair0 == null || typePair1 == null || typePair2 == null)
                        return null;
                
                if (!(ArithmeticUtils.isIntegerType(typePair0.getJavaType())))
                        throw new TypeErrorException(
                                        "Conditional applied to non-integer condition type",
                                        this);
                
                if (!(typePair1.getJavaType() == typePair2.getJavaType() && 
                      (typePair1.getJavaType() instanceof IClangValueType || 
                       typePair1.getJavaType() instanceof StructType)))
                        throw new TypeErrorException(
                                        "Conditional applied to incompatible types (no implicit conversions)",
                                        this);

                return typePair1;
        }
}
