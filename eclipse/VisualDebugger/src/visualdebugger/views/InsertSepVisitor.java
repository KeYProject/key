package visualdebugger.views;

import java.util.HashSet;
import java.util.List;

import org.eclipse.jdt.core.dom.*;

import de.uka.ilkd.key.visualdebugger.VisualDebugger;

public class InsertSepVisitor extends ASTVisitor {
    private int id=0;
    private final HashSet types= new HashSet();
    

    
    
    private ExpressionStatement getSepStatement(AST ast,int id){
        MethodInvocation methodInvocation = ast.newMethodInvocation();
        
        methodInvocation.setExpression(ast.newSimpleName(VisualDebugger.debugClass));
        methodInvocation.setName(ast.newSimpleName(VisualDebugger.sepName));
        
        NumberLiteral literal = ast.newNumberLiteral(""+id);
        methodInvocation.arguments().add(literal);
        ExpressionStatement expressionStatement = ast.newExpressionStatement(methodInvocation);        
        return expressionStatement;
    }
    
    
    private MethodInvocation getSepStatement(AST ast,int id, Expression ex){
        MethodInvocation methodInvocation = ast.newMethodInvocation();
        methodInvocation.setExpression(ast.newSimpleName(VisualDebugger.debugClass));
        //methodInvocation.setExpression(null);
        methodInvocation.setName(ast.newSimpleName(VisualDebugger.sepName)); 
        NumberLiteral literal = ast.newNumberLiteral(""+id);
        ASTNode ex2 = ASTNode.copySubtree(ast, ex);
        
        ASTParser parser = ASTParser.newParser(AST.JLS3); 
        parser.setKind(ASTParser.K_EXPRESSION);
        parser.setSource(ex.toString().toCharArray()); // set source
        //parser.setResolveBindings(true); // we need bindings later on
        ex2 = (ASTNode.copySubtree(ast, (Expression) parser.createAST(null /* IProgressMonitor */)));
        // TODO !!!!!!!!!!!!!!!!!!!!!!!!
        
        methodInvocation.arguments().add(literal);
        methodInvocation.arguments().add((Expression)ex2);

        
        
        //ExpressionStatement expressionStatement = ast.newExpressionStatement(methodInvocation);
        //System.out.println(methodInvocation);
        return methodInvocation;
    }

    
    
    
    
    
    public boolean visit(Block node){
        AST ast = node.getAST();
        for(int i=0; i < node.statements().size();i++){
            id++;
            if (!(node.statements().get(i) instanceof SuperMethodInvocation)
                    && !(node.statements().get(i) instanceof ConstructorInvocation)
                    )
            node.statements().add(i,getSepStatement(ast,id));
            i++;
        }
        return true;
    }
    
    
    public HashSet getTypes(){
        return types;
    }
    
        public void endVisit(FieldAccess node) {
            //System.out.println("FA "+node);
            //node.resolveTypeBinding();
//            System.out.println(node.resolveTypeBinding());   
//            System.out.println(node.resolveFieldBinding());            
//            System.out.println(node.getExpression().resolveTypeBinding());
            
            types.add(node.getExpression().resolveTypeBinding());
            
            
            replaceNode(node.getExpression(), this.getSepStatement(node.getAST(), ++id, node.getExpression()));
        //                IType.resolveType("sdfa");
            
            
           // node.getAST().n
        
        }
        
        
        public void endVisit(QualifiedName node) {

            
            
            if (node.getParent() instanceof QualifiedName)
                return;
            
//            System.out.println("Node " +node);
//            System.out.println("Node q" +node.getQualifier());
//            System.out.println("Node rb" +(node.getQualifier().resolveBinding().getKind()==IBinding.PACKAGE));
            if ((node.getQualifier().resolveBinding().getKind()==IBinding.PACKAGE))
                return;
            //System.out.println("Node rb" +node.getQualifier().resolveTypeBinding().is);
            if (node.getQualifier().resolveTypeBinding().isArray())
                return;
            
            
            //node.getQualifier().resolveTypeBinding();
//            IType t = (IType)node.getQualifier().resolveBinding().getJavaElement();
            
            //node.getQualifier().resolveTypeBinding().getQualifiedName();
            types.add(node.getQualifier().resolveTypeBinding());
            
            //            System.out.println(node.resolveBinding());
            //node.resolveBinding().getJavaElement().
     //       node.getAST().
            //replaceNode(node,node.getAST().newFieldAccess());
//            System.out.println("quf"+node.getQualifier());
//            System.out.println("name" +node.getName());
            MethodInvocation inv = getSepStatement(node.getQualifier().getAST(), ++id, node.getQualifier());
            FieldAccess fa = node.getAST().newFieldAccess();
            
            fa.setName(node.getAST().newSimpleName(node.getName().toString()));
            fa.setExpression(inv);
            
           // System.out.println(fa);
//            System.out.println(fa);
            
            //node.get
            replaceNode(node,fa );
           // this.en
            
        }
        
        public void endVisit(ArrayAccess node){
            Expression index = node.getIndex();
            MethodInvocation inv = getSepStatement(index.getAST(), ++id, index);
            replaceNode(index,inv);
           // this.en
         
        }
        
        
        public void endVisit(MethodInvocation node){
           
        }
        
        
        public void endVisit(CastExpression node){
            
        }
        
        

        public void endVisit(InfixExpression node){
            if (node.getOperator()==InfixExpression.Operator.DIVIDE){
                
            }
             
        }
        
        
//        public void endVisit(IfStatement node){
//            final Expression index = node.getExpression();
//            MethodInvocation inv = getSepStatement(index.getAST(), ++id, index);
//            replaceNode(index,inv);
//            
//        }
        
        
        public void endVisit(ForStatement node){
            final Expression guard = node.getExpression();
            MethodInvocation inv = getSepStatement(guard.getAST(), ++id, guard);
            replaceNode(guard,inv);
            
        }
        
        
        public void endVisit(WhileStatement node){
            final Expression guard = node.getExpression();
            MethodInvocation inv = getSepStatement(guard.getAST(), ++id, guard);
            replaceNode(guard,inv);          
        }
        
        
     public void endVisit(DoStatement node){
            
        }
     
     
     public void endVisit(SwitchStatement node){
         
     }
        


        
        
        
        
        
        
        
        public static void replaceNode(ASTNode oldNode, ASTNode newNode) {
            ASTNode parent = oldNode.getParent();
            StructuralPropertyDescriptor location = oldNode.getLocationInParent();
            if (location.isChildProperty()) {
                parent.setStructuralProperty(location,newNode);
            } else if (location.isChildListProperty()) {
                List list = (List)parent.getStructuralProperty(location);
                int index = list.indexOf(oldNode);
//                System.out.println("Parent "+parent);
//                System.out.println("new Node "+newNode);
                
                list.set(index,newNode);
            }
           

        }
        
        
    public boolean visit(ASTNode node){
       //System.out.println("Node: "+node.toString());
        return true;
    }

}


/*
MethodInvocation methodInvocation = ast.newMethodInvocation();
QualifiedName name = 
    ast.newQualifiedName(
        ast.newSimpleName("System"),
        ast.newSimpleName("out"));
methodInvocation.setExpression(name);
methodInvocation.setName(ast.newSimpleName("println")); 
InfixExpression infixExpression = ast.newInfixExpression();
infixExpression.setOperator(InfixExpression.Operator.PLUS);
StringLiteral literal = ast.newStringLiteral();
literal.setLiteralValue("Hello");
infixExpression.setLeftOperand(literal);
literal = ast.newStringLiteral();
literal.setLiteralValue(" world");
infixExpression.setRightOperand(literal);
methodInvocation.arguments().add(infixExpression);
ExpressionStatement expressionStatement = ast.newExpressionStatement(methodInvocation);
//block.statements().add(expressionStatement);        

System.out.println("BlockNode: "+node.toString());
System.out.println("--------");
System.out.println(expressionStatement);
System.out.println(expressionStatement.getClass());
*/