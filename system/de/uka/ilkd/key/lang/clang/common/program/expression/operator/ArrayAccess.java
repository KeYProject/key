package de.uka.ilkd.key.lang.clang.common.program.expression.operator;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.lang.clang.common.dispatch.IClangProgramDispatcher;
import de.uka.ilkd.key.lang.clang.common.iface.IClangEnvironment;
import de.uka.ilkd.key.lang.clang.common.program.expression.ClangExpressionUtil;
import de.uka.ilkd.key.lang.clang.common.program.iface.BaseClangExpression;
import de.uka.ilkd.key.lang.clang.common.program.iface.IClangExpression;
import de.uka.ilkd.key.lang.clang.common.sort.object.IArraySort;
import de.uka.ilkd.key.lang.clang.common.type.object.ArrayType;
import de.uka.ilkd.key.lang.clang.common.type.value.PointerType;
import de.uka.ilkd.key.lang.common.program.IProgramElement;
import de.uka.ilkd.key.lang.common.type.TypeErrorException;
import de.uka.ilkd.key.util.ExtList;

public final class ArrayAccess extends BaseClangExpression {
        public ArrayAccess(ExtList children, ArrayAccess original) {
                super(children, original);
        }
        
        public IProgramElement copy(ExtList children) {
                return new ArrayAccess(children, this);
        }

        public ArrayAccess(IClangExpression lhs, IClangExpression rhs) {
                super(lhs, rhs);
        }

        public void dispatch(IClangProgramDispatcher p) throws java.lang.Exception {
                p.dispatchArrayAccess(this);
        }
        
        public Boolean isLvalue(IClangEnvironment environment) {
                return ClangExpressionUtil.isLvalue(getExpressionAt(0), environment);
        }

        public KeYJavaType getTypePair(IClangEnvironment environment) {
                KeYJavaType typePairLHS = ClangExpressionUtil.getTypePair(
                                getExpressionAt(0), environment);
                KeYJavaType typePairRHS = ClangExpressionUtil.getTypePair(
                                getExpressionAt(1), environment);

                if (typePairLHS == null || typePairRHS == null)
                        return null;

                if (!((typePairLHS.getJavaType() instanceof ArrayType || typePairLHS.getJavaType() instanceof PointerType)
                        && ArithmeticUtils.isNonPromotableIntegerType(typePairRHS.getJavaType())))
                        throw new TypeErrorException(
                                        "Array access applied to incompatible types (no promotions)",
                                        this);
                
                if (typePairLHS.getJavaType() instanceof ArrayType)
                        return new KeYJavaType(((ArrayType) typePairLHS.getJavaType())
                                .getElemType(), ((IArraySort) typePairLHS
                                .getSort()).getElemSort());
                else
                        return new KeYJavaType(((PointerType) typePairLHS.getJavaType())
                                        .getTargetType(), typePairLHS
                                        .getSort());
        }
}
