package visualdebugger.views;

import org.eclipse.jdt.core.dom.*;
import org.eclipse.jdt.core.dom.InfixExpression.Operator;
import org.eclipse.jface.text.TextSelection;

public class FindStatementVisitor extends ASTVisitor {

    private int currentId = 0;
    
    private int id=0;
    
    private int offset = -1;

    private int length = -1;

    private int toFind;
    
    private Statement statement;

    public FindStatementVisitor(int toFind) {
        super();
        this.toFind = toFind;
    }

    public boolean visit(Block node){
        for(int i=0; i < node.statements().size();i++){
            Statement st = (Statement)node.statements().get(i);
            if (!(st instanceof SuperConstructorInvocation)
                    && !(st instanceof ConstructorInvocation)) {                
                currentId++;
                if (st.getStartPosition() <= toFind
                        && st.getStartPosition() >= offset) {
                    offset = st.getStartPosition();
                    length = st.getLength();
                    statement = st;
                    id=currentId;             
                }            
            }
        }
        return true;
    }

    public TextSelection getTextSelection() {
        //System.out.println("ID "+id);
        if (offset==-1)
            return null;
        else return new TextSelection(offset, length);
    }
    
    public int getStatementId(){
        return id;
    }
    
    public Statement getStatement(){
        return statement;
    }
    
    
    public void endVisit(FieldAccess node) {
        currentId++;
    }
    
    
    public void endVisit(QualifiedName node) {
        if (node.getParent() instanceof QualifiedName)
            return;
        
        if ((node.getQualifier().resolveBinding().getKind()==IBinding.PACKAGE))
            return;

        
        if (node.getQualifier().resolveTypeBinding().isArray())
            return;
        currentId++;
    }
    
   
    public void endVisit(ArrayAccess node){
        currentId++;
    }
    
    public void endVisit(InfixExpression node) {
        if (node.getOperator() == Operator.DIVIDE || 
                node.getOperator() == Operator.REMAINDER) {
            currentId++;
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
        }   
    }

    /**
     * find also ids for single line bodies of control statements
     * @param st
     */
    private void checkBody(Statement st) {
        if (!(st instanceof Block)) {
            currentId++;
            if (st.getStartPosition() <= toFind
                    && st.getStartPosition() >= offset) {
                offset = st.getStartPosition();
                length = st.getLength();
                statement = st;
                id=currentId;               
            }            
        }        
    }
   
    public void endVisit(IfStatement node) {
        checkBody(node.getThenStatement());
        if (node.getElseStatement() != null) {
            checkBody(node.getElseStatement());
        }
    }
    
    public void endVisit(DoStatement node) {
        currentId++;
        checkBody(node.getBody());
    }

    public void endVisit(ForStatement node) {
        currentId++;
        checkBody(node.getBody());
    }
    
    public void endVisit(WhileStatement node) {
        currentId++;
        checkBody(node.getBody());
    }
}
