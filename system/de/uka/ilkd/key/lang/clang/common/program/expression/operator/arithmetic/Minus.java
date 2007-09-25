package de.uka.ilkd.key.lang.clang.common.program.expression.operator.arithmetic;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.lang.clang.common.dispatch.IClangProgramDispatcher;
import de.uka.ilkd.key.lang.clang.common.iface.IClangEnvironment;
import de.uka.ilkd.key.lang.clang.common.program.expression.ClangExpressionUtil;
import de.uka.ilkd.key.lang.clang.common.program.expression.operator.ArithmeticUtils;
import de.uka.ilkd.key.lang.clang.common.program.iface.BaseClangExpression;
import de.uka.ilkd.key.lang.clang.common.program.iface.IClangExpression;
import de.uka.ilkd.key.lang.clang.common.type.IClangInstantiableObjectType;
import de.uka.ilkd.key.lang.clang.common.type.value.PointerType;
import de.uka.ilkd.key.lang.common.program.IProgramElement;
import de.uka.ilkd.key.lang.common.type.TypeErrorException;
import de.uka.ilkd.key.util.ExtList;

public final class Minus extends BaseClangExpression {
        KeYJavaType castTypePair;

        public Minus(ExtList children, Minus original) {
                super(children, original);
                this.castTypePair = original.castTypePair;
        }
        
        public IProgramElement copy(ExtList children) {
                return new Minus(children, this);
        }
        
        public Minus(IClangExpression lhs, IClangExpression rhs, KeYJavaType castTypePair) {
                super(lhs, rhs);
                this.castTypePair = castTypePair;
        }

        public Minus(IClangExpression lhs, IClangExpression rhs) {
                this(lhs, rhs, null);
        }

        public void dispatch(IClangProgramDispatcher p) throws java.lang.Exception {
                p.dispatchMinus(this);
        }

        public Boolean isLvalue(IClangEnvironment environment) {
                return Boolean.FALSE;
        }

        public KeYJavaType getTypePair(IClangEnvironment environment) {
                KeYJavaType typePairLHS = ClangExpressionUtil.getTypePair(
                                getExpressionAt(0), environment);
                KeYJavaType typePairRHS = ClangExpressionUtil.getTypePair(
                                getExpressionAt(1), environment);

                if (typePairLHS == null || typePairRHS == null)
                        return null;

                // if "arithm - arithm"
                if (typePairLHS.getJavaType() == typePairRHS.getJavaType()
                                && ArithmeticUtils
                                                .isNonPromotableIntegerType(typePairLHS
                                                                .getJavaType())
                                && ArithmeticUtils
                                                .isNonPromotableType(typePairRHS
                                                                .getJavaType()))
                        return typePairLHS;
                // if "pointer - integer"
                else if (typePairLHS.getJavaType() instanceof PointerType
                                && ((PointerType) typePairLHS.getJavaType())
                                                .getTargetType() instanceof IClangInstantiableObjectType
                                && ArithmeticUtils
                                                .isNonPromotableIntegerType(typePairRHS
                                                                .getJavaType()))
                        return typePairLHS;
                // if "pointer - pointer"
                else if (typePairLHS.getJavaType() == typePairRHS.getJavaType()
                                && typePairLHS.getJavaType() instanceof PointerType
                                && typePairRHS.getJavaType() instanceof PointerType) {
                        if (castTypePair == null)
                                throw new TypeErrorException(
                                                "Minus applied to pointers must be within a type cast",
                                                this);
                        if (ArithmeticUtils.isNonPromotableType(castTypePair
                                        .getJavaType()))
                                return castTypePair;
                }

                throw new TypeErrorException(
                                "Minus applied to incompatible types (no promotions)",
                                this);
        }
}
