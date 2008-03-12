package visualdebugger.astops;

import java.util.*;

import org.eclipse.jdt.core.dom.*;

public class PositionFinder extends ASTVisitor {
    private Set<SimpleName> oldLocalVariables = new HashSet<SimpleName>();
    private Set<SimpleName> newLocalVariables = new HashSet<SimpleName>();

    public PositionFinder(Set<SimpleName> oldLocalVariables) {
        super();
        this.oldLocalVariables = oldLocalVariables;
    }

    public boolean visit(SimpleName sn) {
        System.out.println("################" + sn.toString());
        IBinding binding = sn.resolveBinding();
        if(binding == null) System.out.println("Binding null");
        if (binding instanceof IVariableBinding) {
            IVariableBinding vb = (IVariableBinding) binding;
            System.out.println("declaring method " + vb.getDeclaringMethod());

        }
        return false;
    }

    public Set<SimpleName> getLocalVariables() {
        return newLocalVariables;
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
}