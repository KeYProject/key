package de.uka.ilkd.key.lang.clang.common.program.expression.operator;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.lang.clang.common.dispatch.IClangProgramDispatcher;
import de.uka.ilkd.key.lang.clang.common.iface.IClangEnvironment;
import de.uka.ilkd.key.lang.clang.common.program.expression.ClangExpressionUtil;
import de.uka.ilkd.key.lang.clang.common.program.expression.operator.arithmetic.Divide;
import de.uka.ilkd.key.lang.clang.common.program.iface.BaseClangExpression;
import de.uka.ilkd.key.lang.clang.common.program.iface.IClangExpression;
import de.uka.ilkd.key.lang.clang.common.program.iface.IClangTypeReference;
import de.uka.ilkd.key.lang.clang.common.type.IClangValueType;
import de.uka.ilkd.key.lang.common.program.IProgramElement;
import de.uka.ilkd.key.lang.common.programsv.BaseProgramSV;
import de.uka.ilkd.key.lang.common.type.TypeErrorException;
import de.uka.ilkd.key.util.ExtList;

public final class TypeCast extends BaseClangExpression {

        private IClangTypeReference typeReference;

        public TypeCast(IClangExpression expression, IClangTypeReference typeReference) {
                super(expression);
                this.typeReference = typeReference;
        }

        public TypeCast(ExtList children, TypeCast original) {
                super(children, original);
                this.typeReference = (IClangTypeReference) children
                                .get(IClangTypeReference.class);
        }
        
        public IProgramElement copy(ExtList children) {
                return new TypeCast(children, this);
        }
        
        public IClangTypeReference getTypeReference() {
                return typeReference;
        }

        public int getChildCount() {
                return 1 + super.getExpressionCount();
        }

        public IProgramElement getProgramElementAt(int index) {
                if (index == 0)
                        return typeReference;
                else
                        return super.getExpressionAt(index - 1);
        }

        public void dispatch(IClangProgramDispatcher p) throws java.lang.Exception {
                p.dispatchTypeCast(this);
        }

        public Boolean isLvalue(IClangEnvironment environment) {
                return Boolean.FALSE;
        }

        public KeYJavaType getTypePair(IClangEnvironment environment) {
                KeYJavaType typePair = ClangExpressionUtil.getTypePair(
                                getExpressionAt(0), environment);

                if (typeReference instanceof BaseProgramSV || typePair == null)
                        return null;

                if (!(typeReference.getTypePair().getJavaType() instanceof IClangValueType && typePair
                                .getJavaType() instanceof IClangValueType))
                        throw new TypeErrorException(
                                        "Type cast applied to incompatible types",
                                        this);

                return typeReference.getTypePair();
        }
}
