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

}
