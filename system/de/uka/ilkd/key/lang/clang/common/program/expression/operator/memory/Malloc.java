package de.uka.ilkd.key.lang.clang.common.program.expression.operator.memory;

import de.uka.ilkd.key.lang.common.program.IProgramElement;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.lang.clang.common.dispatch.IClangProgramDispatcher;
import de.uka.ilkd.key.lang.clang.common.iface.IClangEnvironment;
import de.uka.ilkd.key.lang.clang.common.program.expression.operator.arithmetic.Divide;
import de.uka.ilkd.key.lang.clang.common.program.iface.BaseClangExpression;
import de.uka.ilkd.key.lang.clang.common.program.iface.IClangTypeReference;
import de.uka.ilkd.key.lang.clang.common.type.IClangObjectType;
import de.uka.ilkd.key.lang.common.programsv.BaseProgramSV;
import de.uka.ilkd.key.lang.common.type.TypeErrorException;
import de.uka.ilkd.key.util.ExtList;

public final class Malloc extends BaseClangExpression {

        IClangTypeReference typeReference;
        KeYJavaType resultTypePair;

        public Malloc(IClangTypeReference typeReference, KeYJavaType resultTypePair) {
                super();
                this.typeReference = typeReference;
                this.resultTypePair = resultTypePair;
        }

        public Malloc(ExtList children, Malloc original) {
                super(children, original);
                this.typeReference = (IClangTypeReference)children.get(IClangTypeReference.class);
                this.resultTypePair = original.resultTypePair;
        }
        
        public IProgramElement copy(ExtList children) {
                return new Malloc(children, this);
        }
        
        public IClangTypeReference getTypeReference() {
                return typeReference;
        }

        public IProgramElement getProgramElementAt(int index) {
                if (index == 0)
                        return typeReference;
                else
                        throw new ArrayIndexOutOfBoundsException();
        }

        public void dispatch(IClangProgramDispatcher p) throws java.lang.Exception {
                p.dispatchMalloc(this);
        }
        
        public Boolean isLvalue(IClangEnvironment environment) {
                return Boolean.FALSE;
        }
        
        public KeYJavaType getTypePair(IClangEnvironment environment) {
                if (typeReference instanceof BaseProgramSV)
                        return null;
                
                if (!(typeReference.getTypePair().getJavaType() instanceof IClangObjectType))
                        throw new TypeErrorException("Malloc applied to incompatible type", this);

                return resultTypePair;
        }
}
