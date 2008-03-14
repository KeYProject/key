package visualdebugger.astops;

import java.util.*;

import org.eclipse.jdt.core.dom.*;

public class PositionFinder extends ASTVisitor {
    private Set<SimpleName> oldLocalVariables = new HashSet<SimpleName>();
    private Set<SimpleName> newLocalVariables = new HashSet<SimpleName>();
    private String method;

    public PositionFinder(Set<SimpleName> localVariables,
            String methodOfInterest) {
        super();
        this.oldLocalVariables = localVariables;
        this.method = methodOfInterest;
    }

    public boolean visit(SimpleName sn) {

        IBinding binding = sn.resolveBinding();

        if (binding instanceof IVariableBinding) {
            IVariableBinding vb = (IVariableBinding) binding;

            String thisMethod = vb.getDeclaringMethod() + "";
            if (thisMethod.equals(method) && !vb.isField()) {
                for (SimpleName simpleName : oldLocalVariables) {
//TODO eliminate duplicates
                    if (simpleName.toString().equals(sn.toString())) {
                        System.out
                                .println("+++++  " + sn + " " + vb.hashCode());
                            newLocalVariables.add(sn);
                            
                        }

                    }
                }
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