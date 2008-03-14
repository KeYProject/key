package visualdebugger.astops;

import java.util.HashSet;
import java.util.Set;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.core.dom.*;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.Document;
import org.eclipse.text.edits.MalformedTreeException;
import org.eclipse.text.edits.TextEdit;
import org.eclipse.text.edits.UndoEdit;

import visualdebugger.views.InsertSepVisitor;
import de.uka.ilkd.key.visualdebugger.VisualDebugger;

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
     * Parses the ICompilationUnit.
     * 
     * @param unit
     *            the unit
     * @param pm
     *            the progressmonitor
     * 
     * @return the compilation unit
     */
    public static CompilationUnit parseSource(String source,
            IProgressMonitor pm) {
        try {
            ASTParser parser = ASTParser.newParser(AST.JLS3);
            parser.setSource(source.toCharArray());
            //FIXME not working
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
