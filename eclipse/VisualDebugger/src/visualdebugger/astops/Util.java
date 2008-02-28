package visualdebugger.astops;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.Set;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.jdt.core.dom.AST;
import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.ASTParser;
import org.eclipse.jdt.core.dom.CompilationUnit;
import org.eclipse.jdt.core.dom.Expression;
import org.eclipse.jdt.core.dom.IVariableBinding;
import org.eclipse.jdt.core.dom.InfixExpression;
import org.eclipse.jdt.core.dom.SimpleName;

/**
 * The Class Util.
 */
public final class Util {

    /**
     * Gets the operands.
     * 
     * @param operand -
     *            An InfixExpression, from which all operands that might be
     *            local variables are extracted.
     * 
     * Note: No literals, field access', etc. are taken into account
     * 
     * @return the operands
     */
    public static Set<SimpleName> getOperands(Expression operand) {

        Set<SimpleName> operands = new HashSet<SimpleName>();
        if (operand instanceof SimpleName) {
            operands.add((SimpleName) operand);
            return operands;
        } else {
            if (operand instanceof InfixExpression) {
                InfixExpression ie = (InfixExpression) operand;
                operands.addAll(getOperands(ie.getLeftOperand()));
                operands.addAll(getOperands(ie.getRightOperand()));
            }
        }
        return operands;
    }

    /**
     * Extract local variables for method.
     * 
     * @param method
     *            the method
     * @param allLocalVariables
     *            the all local variables
     * 
     * @return the linked list< i variable binding>
     */
    public static LinkedList<IVariableBinding> extractLocalVariablesForMethod(
            IMethod method, Set<IVariableBinding> allLocalVariables) {

        LinkedList<IVariableBinding> localVariableBindings = new LinkedList<IVariableBinding>();
        for (IVariableBinding variableBinding : allLocalVariables) {
            if (method.getElementName().equals(
                    variableBinding.getDeclaringMethod().getName())) {
                localVariableBindings.add(variableBinding);
            }
        }

        return localVariableBindings;
    }

    /**
     * Extract local variables for expression.
     * 
     * @param node
     *            the node
     * @param localVariableBindings
     *            the local variable bindings
     * 
     * @return the set< i variable binding>
     */
    public static Set<IVariableBinding> extractLocalVariablesForExpression(
            Expression node, LinkedList<IVariableBinding> localVariableBindings) {

        Set<IVariableBinding> localVariables = new HashSet<IVariableBinding>();
        if (node instanceof InfixExpression) {

            InfixExpression ie = (InfixExpression) node;

            Set<SimpleName> operands = getOperands(ie);
            System.out.println("left " + ie.getLeftOperand());
            System.out.println("class " + ie.getLeftOperand().getClass());
            System.out.println("found " + operands.size() + " operands");

            for (SimpleName candidate : operands) {

                for (IVariableBinding localVariableBinding : localVariableBindings) {
                    String a = localVariableBinding.getName();
                    String b = candidate.toString();
                    if (a.equals(b)) {
                        localVariables.add(localVariableBinding);
                    }
                }
            }
        }
        return localVariables;
    }

    /**
     * Gets the loc var inf.
     * 
     * @param cu
     *            the cu
     * @param localVariableBinding
     *            the local variable binding
     * 
     * @return the loc var inf
     */
    public static LinkedList<String[]> getLocVarInf(CompilationUnit cu,
            Set<IVariableBinding> localVariableBinding) {
        
        LinkedList<String[]> informations = new LinkedList<String[]>();
        for (IVariableBinding variableBinding : localVariableBinding) {
            
            ASTNode astnode = cu.findDeclaringNode(variableBinding);
            String[] information = new String[3];
            information[0] = variableBinding.getType().getName() + ""; // type
            information[1] = variableBinding.getName() + ""; // name
            information[2] = astnode.getStartPosition() + ""; // offset
            informations.add(information);
        }
        return informations;
    }

    /**
     * Parses the ICompilationUnit.
     * 
     * @param unit
     *            the unit
     * @param pm
     *            the progressmonitor
     * 
     * @return the compilation unit
     */
    public static CompilationUnit parse(ICompilationUnit unit,
            IProgressMonitor pm) {
        try {
            ASTParser parser = ASTParser.newParser(AST.JLS3);
            parser.setKind(ASTParser.K_COMPILATION_UNIT);
            parser.setSource(unit);
            parser.setResolveBindings(true);
            return (CompilationUnit) parser.createAST(pm);
        } catch (Throwable t) {
            t.printStackTrace();
            return null;
        }
    }

    /**
     * Parses the Expression given as String.
     * 
     * @param expression
     *            the expression
     * @param pm
     *            the pm
     * 
     * @return the expression
     */
    public static Expression parse(String expression, IProgressMonitor pm) {
        try {
            ASTParser expressionparser = ASTParser.newParser(AST.JLS3);
            expressionparser.setKind(ASTParser.K_EXPRESSION);
            expressionparser.setSource(expression.toCharArray());
            expressionparser.setResolveBindings(true);
            return (Expression) expressionparser.createAST(pm);
        } catch (Throwable t) {
            t.printStackTrace();
            return null;
        }
    }

    /**
     * Detect local variables.
     * 
     * @param cu
     *            the cu
     * 
     * @return the set< i variable binding>
     */
    public static Set<IVariableBinding> detectLocalVariables(CompilationUnit cu) {

        LocalVariableDetector localVariableDetector = new LocalVariableDetector();
        localVariableDetector.process(cu);
        return localVariableDetector.getLocalVariableManagers().keySet();
    }

}
