package visualdebugger.astops;

import java.util.*;

import org.eclipse.jdt.core.dom.*;

public class LocalVariableDetector extends ASTVisitor {
    Set<SimpleName> localVariables = new HashSet<SimpleName>();
    private Expression expr;

    public LocalVariableDetector(Expression e){
        this.expr = e;
    }    
    
    public boolean visit(VariableDeclarationStatement node) {
        
        VariableDeclarationFragment fragment = (VariableDeclarationFragment) node.fragments().get(0);
        Expression initializer = fragment.getInitializer();
        String e = initializer.toString();
        if(e.equals(expr.toString())){

            Helper helper = new Helper();
            initializer.accept(helper);

        }
        return false;
    }

    
    public Set<SimpleName> getLocalVariables() {
        return localVariables;
    }

    /**
     * Starts the process.
     *
     * @param unit
     *            the AST root node. Bindings have to have been resolved.
     */
    public void process(CompilationUnit unit) {
        unit.accept(this);
    }
    
    class Helper extends ASTVisitor{
        
        public boolean visit(SimpleName sn) {
            IBinding binding =sn.resolveBinding();
            if (binding instanceof IVariableBinding) {
                IVariableBinding vb = (IVariableBinding) binding;
                if (!vb.isField()) {
                    localVariables.add(sn);
                }
            }
            return false;
        }
        
    }
}