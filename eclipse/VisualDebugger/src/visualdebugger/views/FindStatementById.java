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
            final Object stmnt = node.statements().get(i);
            if (!(stmnt instanceof SuperConstructorInvocation)
                    && !(stmnt instanceof ConstructorInvocation)) {                
                currentId++;
                if (currentId == idToFind) {
                    st = (Statement) stmnt;
                }
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
    
        
        if (node.getQualifier().resolveTypeBinding() == null) {
            return;
        }
        currentId++;
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
        final Statement body = node.getBody();        
        checkControlStatementWithoutBlocks(body);
    }

    public void endVisit(WhileStatement node) {
        final Expression guard = node.getExpression();
        currentId++;
        if (currentId == idToFind) {
            expr = guard;
        }
        final Statement body = node.getBody();
        checkControlStatementWithoutBlocks(body);
    }

    private void checkControlStatementWithoutBlocks(final Statement body) {
        if (!(body instanceof Block)) {
            currentId++;
            if (currentId == idToFind) {
                st = body; 
            }
        }
    }
    
    /**
     * The guard of a "do-while" statement is enclosed by a <code>Debug.sep</code>
     * statement. 
     * 
     * If the body of the loop is only a single statement and not a block, we have to enclose it
     * in a block and to add a <code>Debug.sep</code> statement as first statement of the body. 
     */
    public void endVisit(DoStatement node) {
        final Expression guard = node.getExpression();
        currentId++;
        if (currentId == idToFind) {
            expr = guard;
        }
        final Statement body = node.getBody();
        checkControlStatementWithoutBlocks(body);
    }

    /**
     * Ensures that existing then and else statements use blocks and their first statement 
     * is a breakpoint 
     */
    public void endVisit(IfStatement node) {
        final Statement thenStmnt = node.getThenStatement();
        checkControlStatementWithoutBlocks(thenStmnt);
        final Statement elseStmnt = node.getElseStatement();
        if (elseStmnt != null) {
            checkControlStatementWithoutBlocks(elseStmnt);
        }
    }


    public Statement getStatement() {
        return st;
    }

    public Expression getExpression() {
        return expr;
    }

}
