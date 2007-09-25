package visualdebugger.views;

import org.eclipse.jdt.core.dom.*;
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

/*    public void preVisit(ASTNode node) {
        
       
        if (node instanceof Statement) {
            currentId++;
            System.out.println("st "+id+""+node);
            Statement st = (Statement) node;
            if (st.getStartPosition() < toFind
                    && st.getStartPosition() > offset) {
                offset = st.getStartPosition();
                length = st.getLength();
                id=currentId;
            }
        }
    
    

    }*/
    
    public boolean visit(Block node){
        for(int i=0; i < node.statements().size();i++){
            currentId++;
            Statement st = (Statement)node.statements().get(i);
            if (st.getStartPosition() <= toFind
                    && st.getStartPosition() >= offset) {
                offset = st.getStartPosition();
                length = st.getLength();
                statement = st;
                id=currentId;
               
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
    //    System.out.println(node+" "+currentId);
//        if(currentId==idToFind){
//            expr=node;
//        }
    }
    
    
    public void endVisit(QualifiedName node) {

        
        
        if (node.getParent() instanceof QualifiedName)
            return;
        
        if ((node.getQualifier().resolveBinding().getKind()==IBinding.PACKAGE))
            return;

        
        if (node.getQualifier().resolveTypeBinding().isArray())
            return;
        currentId++;
    //    System.out.println(node+" "+currentId);
//        if(currentId==idToFind){
//            expr=node;
//        }

    }
    
    
    
    public void endVisit(ArrayAccess node){
        currentId++;
        //    System.out.println(node+" "+currentId);
//            if(currentId==idToFind){
//                expr=node;
//            }

    }
    
    
//    public void endVisit(IfStatement node){
//        final Expression index = node.getExpression();
//        currentId++;
//    }
    
    
    public void endVisit(ForStatement node){
        final Expression guard = node.getExpression();
        currentId++;
    }
    
    
    public void endVisit(WhileStatement node){
        final Expression guard = node.getExpression();
        currentId++;
    }
    
    
    
    
    

}
