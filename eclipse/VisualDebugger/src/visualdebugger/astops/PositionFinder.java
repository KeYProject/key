package visualdebugger.astops;

import java.util.*;

import org.eclipse.jdt.core.dom.*;

/**
 * The Class PositionFinder.
 * 
 * This Class enumerates every IVariableBinding of the given method that is either a parameter or
 * a local variable.
 */
public class PositionFinder extends ASTVisitor {

    /** The method. */
    private String method;

    /** The position info. */
    private HashMap<IVariableBinding, Integer> positionInfo = new HashMap<IVariableBinding, Integer>();
    /** The position counter. */
    private int count = 0;

    /**
     * Instantiates a new position finder.

     * @param methodOfInterest
     *            the method of interest
     */
    public PositionFinder(String methodOfInterest) {
        super();
        this.method = methodOfInterest;
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.eclipse.jdt.core.dom.ASTVisitor#visit(org.eclipse.jdt.core.dom.SimpleName)
     */
    public boolean visit(SimpleName sn) {

        IBinding binding = sn.resolveBinding();

        if (binding instanceof IVariableBinding) {
            IVariableBinding vb = (IVariableBinding) binding;

            String thisMethod = vb.getDeclaringMethod() + "";
            if (thisMethod.equals(method) && !vb.isField()) {
                if (vb.isParameter()) {
                    if (!(positionInfo.containsKey(vb)))
                        positionInfo.put(vb, count++);
                }
            }
        }
        return false;
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.eclipse.jdt.core.dom.ASTVisitor#visit(org.eclipse.jdt.core.dom.VariableDeclarationFragment)
     */
    public boolean visit(VariableDeclarationFragment vdf) {

        IBinding binding = vdf.resolveBinding();

        if (binding instanceof IVariableBinding) {
            IVariableBinding vb = (IVariableBinding) binding;

            String thisMethod = vb.getDeclaringMethod() + "";
            if (thisMethod.equals(method) && !vb.isField()) {
                vdf.accept(new Helper());
            }
        }
        return false;
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

    /**
     * The Class Helper.
     */
    class Helper extends ASTVisitor {

        /*
         * (non-Javadoc)
         * 
         * @see org.eclipse.jdt.core.dom.ASTVisitor#visit(org.eclipse.jdt.core.dom.SimpleName)
         */
        public boolean visit(SimpleName sn) {
            IBinding binding = sn.resolveBinding();

            if (binding instanceof IVariableBinding) {
                IVariableBinding vb = (IVariableBinding) binding;
                if (!(positionInfo.containsKey(vb)))
                    positionInfo.put(vb, count++);
            }
            return false;
        }
    }

    /**
     * Gets the position info.
     * 
     * @return the position info
     */
    public HashMap<IVariableBinding, Integer> getPositionInfo() {
        return positionInfo;
    }
}