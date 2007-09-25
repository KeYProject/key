package de.uka.ilkd.key.lang.clang.common.program.expression.operator.memory;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.lang.clang.common.dispatch.IClangProgramDispatcher;
import de.uka.ilkd.key.lang.clang.common.iface.IClangEnvironment;
import de.uka.ilkd.key.lang.clang.common.program.expression.ClangExpressionUtil;
import de.uka.ilkd.key.lang.clang.common.program.expression.operator.ArithmeticUtils;
import de.uka.ilkd.key.lang.clang.common.program.iface.BaseClangExpression;
import de.uka.ilkd.key.lang.clang.common.program.iface.IClangExpression;
import de.uka.ilkd.key.lang.clang.common.program.iface.IClangTypeReference;
import de.uka.ilkd.key.lang.clang.common.program.statement.BlockFrame;
import de.uka.ilkd.key.lang.clang.common.type.IClangObjectType;
import de.uka.ilkd.key.lang.common.program.IProgramElement;
import de.uka.ilkd.key.lang.common.programsv.BaseProgramSV;
import de.uka.ilkd.key.lang.common.type.TypeErrorException;
import de.uka.ilkd.key.util.ExtList;

public final class Calloc extends BaseClangExpression {

        private IClangTypeReference typeReference;

        private KeYJavaType resultTypePair;

        public Calloc(IClangExpression expression, IClangTypeReference typeReference,
                        KeYJavaType resultTypePair) {
                super(expression);
                this.resultTypePair = resultTypePair;
                this.typeReference = typeReference;
        }

        public Calloc(ExtList children, Calloc original) {
                super(children, original);
                this.typeReference = (IClangTypeReference) children
                                .get(IClangTypeReference.class);
                this.resultTypePair = original.resultTypePair;
        }
        
        public IProgramElement copy(ExtList children) {
                return new Calloc(children, this);
        }
        
        public IClangTypeReference getTypeReference() {
                return typeReference;
        }

        public int getChildCount() {
                return super.getChildCount() + 1;
        }

        public IProgramElement getProgramElementAt(int index) {
                if (index == 0)
                        return typeReference;
                else
                        return super.getExpressionAt(index - 1);
        }

        public void dispatch(IClangProgramDispatcher p) throws java.lang.Exception {
                p.dispatchCalloc(this);
        }

        public Boolean isLvalue(IClangEnvironment environment) {
                return Boolean.FALSE;
        }

        public KeYJavaType getTypePair(IClangEnvironment environment) {
                KeYJavaType typePair = ClangExpressionUtil.getTypePair(
                                getExpressionAt(0), environment);

                if (typePair == null || typeReference instanceof BaseProgramSV)
                        return null;

                if (!(typeReference.getTypePair().getJavaType() instanceof IClangObjectType
                                && ArithmeticUtils
                                                .isNonPromotableIntegerType(typePair
                                                                .getJavaType()) && ArithmeticUtils
                                .isNonPromotableIntegerType(typePair
                                                .getJavaType())))
                        throw new TypeErrorException(
                                        "Calloc applied to incompatible types",
                                        this);

                return resultTypePair;
        }
}
