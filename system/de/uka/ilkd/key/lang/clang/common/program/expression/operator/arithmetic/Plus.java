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

public final class Plus extends BaseClangExpression {

        public Plus(ExtList children, Plus original) {
                super(children, original);
        }
        
        public IProgramElement copy(ExtList children) {
                return new Plus(children, this);
        }
        
        public Plus(IClangExpression lhs, IClangExpression rhs) {
                super(lhs, rhs);
        }

        public int getArity() {
                return 2;
        }

        public void dispatch(IClangProgramDispatcher p) throws java.lang.Exception {
                p.dispatchPlus(this);
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

                // if "arithm + arithm"
                if (typePairLHS.getJavaType() == typePairRHS.getJavaType()
                                && ArithmeticUtils
                                                .isNonPromotableType(typePairLHS
                                                                .getJavaType())
                                && ArithmeticUtils
                                                .isNonPromotableType(typePairRHS
                                                                .getJavaType()))
                        return typePairLHS;
                // if "pointer + integer"
                else if (typePairLHS.getJavaType() instanceof PointerType
                                && ((PointerType) typePairLHS.getJavaType())
                                                .getTargetType() instanceof IClangInstantiableObjectType
                                && ArithmeticUtils
                                                .isNonPromotableIntegerType(typePairRHS
                                                                .getJavaType()))
                        return typePairLHS;
                // if "integer + pointer"
                else if (typePairRHS.getJavaType() instanceof PointerType
                                && ((PointerType) typePairRHS.getJavaType())
                                .getTargetType() instanceof IClangInstantiableObjectType
                                && ArithmeticUtils
                                                .isNonPromotableIntegerType(typePairLHS
                                                                .getJavaType()))
                        return typePairRHS;
                else
                        throw new TypeErrorException(
                                        "Plus applied to incompatible types (no promotions)",
                                        this);
        }
}
