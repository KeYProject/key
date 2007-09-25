package de.uka.ilkd.key.lang.clang.common.program.expression.operator;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.lang.clang.common.dispatch.IClangProgramDispatcher;
import de.uka.ilkd.key.lang.clang.common.iface.IClangEnvironment;
import de.uka.ilkd.key.lang.clang.common.program.expression.ClangExpressionUtil;
import de.uka.ilkd.key.lang.clang.common.program.iface.BaseClangExpression;
import de.uka.ilkd.key.lang.clang.common.program.iface.IClangExpression;
import de.uka.ilkd.key.lang.clang.common.program.statement.BlockFrame;
import de.uka.ilkd.key.lang.clang.common.type.value.PointerType;
import de.uka.ilkd.key.lang.common.program.IProgramElement;
import de.uka.ilkd.key.lang.common.type.TypeErrorException;
import de.uka.ilkd.key.util.ExtList;

public final class Dereference extends BaseClangExpression {
    public Dereference(IClangExpression expression) {
        super(expression);
    }

    public Dereference(ExtList children, Dereference original) {
        super(children, original);
    }
    
    public IProgramElement copy(ExtList children) {
            return new Dereference(children, this);
    }
    
    public void dispatch(IClangProgramDispatcher p) throws java.lang.Exception {
        p.dispatchDereference(this);
    }
    
    public Boolean isLvalue(IClangEnvironment environment) {
            return Boolean.TRUE;
    }
    
    public KeYJavaType getTypePair(IClangEnvironment environment) {
        KeYJavaType typePair = ClangExpressionUtil.getTypePair(getExpressionAt(0), environment);
        if (typePair == null)
                return null;
        
        if (!(typePair.getJavaType() instanceof PointerType))
                throw new TypeErrorException("Dereference applied to non-pointer type", this);
        
        Type targetType = ((PointerType)typePair.getJavaType()).getTargetType();
        return new KeYJavaType(targetType, typePair.getSort());
    }

}
