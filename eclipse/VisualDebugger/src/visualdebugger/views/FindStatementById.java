package visualdebugger.views;

import org.eclipse.jdt.core.dom.*;
import org.eclipse.jdt.core.dom.InfixExpression.Operator;

import de.uka.ilkd.key.visualdebugger.SourceElementId;

public class FindStatementById extends ASTVisitor {

    private int currentId = 0;

    private final int idToFind;

    private Statement st = null;

    private Expression expr = null;

    
    public FindStatementById(SourceElementId idToFind) {
        super();       
        this.idToFind = idToFind.getId();        
    }

    public boolean visit(Block node) {        
        for (int i = 0; i < node.statements().size(); i++) {
            currentId++;
            // System.out.println(node.statements().get(i)+" "+currentId);
            if (currentId == idToFind) {
                st = (Statement) node.statements().get(i);
            }
        }
        return true;
    }

    public void endVisit(FieldAccess node) {
        final ITypeBinding expressionTypeBinding = node.getExpression().resolveTypeBinding();
        if (expressionTypeBinding != null) {
            currentId++;
            if (currentId == idToFind) {
                expr = node;
            }
        }
    }

    public void endVisit(QualifiedName node) {

        if (node.getParent() instanceof QualifiedName)
            return;

        if ((node.getQualifier().resolveBinding().getKind() == IBinding.PACKAGE))
            return;

        final IBinding simpleNameBinding = node.getName().resolveBinding();
        
        if (simpleNameBinding == null || 
                Modifier.isStatic(simpleNameBinding.getModifiers())) {           
            return;
        }
    
        
        if (node.getQualifier().resolveTypeBinding().isArray())
            return;
        currentId++;
        // System.out.println(node+" "+currentId);
        if (currentId == idToFind) {
            expr = node;
        }

    }

    public void endVisit(ArrayAccess node) {
        currentId++;
        // System.out.println(node+" "+currentId);
        if (currentId == idToFind) {
            expr = node;
        }

    }

    public void endVisit(InfixExpression node) {
        if (node.getOperator() == Operator.DIVIDE || 
                node.getOperator() == Operator.REMAINDER) {
            currentId++;
            if (currentId == idToFind) {
                expr = node.getRightOperand();
            }
        }        
    }

    /**
     * Division-by-zero ArithmeticExceptions can occur when evaluating
     * the division or remainder composite assignment operator. 
     */
    public void endVisit(Assignment node) {
        if (node.getOperator() == Assignment.Operator.DIVIDE_ASSIGN || 
                node.getOperator() == Assignment.Operator.REMAINDER_ASSIGN) {
            currentId++;
            if (currentId == idToFind) {
                expr = node.getRightHandSide();
            }
        }   
    }

    
    public void endVisit(ForStatement node) {
        final Expression guard = node.getExpression();
        currentId++;
        if (currentId == idToFind) {
            expr = guard;
        }
    }

    public void endVisit(WhileStatement node) {
        final Expression guard = node.getExpression();
        currentId++;
        if (currentId == idToFind) {
            expr = guard;
        }
    }

    public Statement getStatement() {
        return st;
    }

    public Expression getExpression() {
        return expr;
    }

}
