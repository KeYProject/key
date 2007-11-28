package visualdebugger.views;

import java.util.HashSet;
import java.util.List;

import org.eclipse.jdt.core.dom.*;

import de.uka.ilkd.key.visualdebugger.VisualDebugger;

public class InsertSepVisitor extends ASTVisitor {
    
    public static void replaceNode(ASTNode oldNode, ASTNode newNode) {
        ASTNode parent = oldNode.getParent();
        StructuralPropertyDescriptor location = oldNode.getLocationInParent();
        if (location.isChildProperty()) {
            parent.setStructuralProperty(location, newNode);
        } else if (location.isChildListProperty()) {
            List list = (List) parent.getStructuralProperty(location);
            int index = list.indexOf(oldNode);           
            list.set(index, newNode);
        }
    }

    private int id = 0;

    private final HashSet types = new HashSet();

    public void endVisit(ArrayAccess node) {
        Expression index = node.getIndex();
        MethodInvocation inv = getSepStatement(index.getAST(), ++id, index);
        replaceNode(index, inv);
    }


    public void endVisit(FieldAccess node) {
        final ITypeBinding expressionTypeBinding = node.getExpression().resolveTypeBinding();
        if (expressionTypeBinding != null) {

            types.add(expressionTypeBinding);

            replaceNode(node.getExpression(), getSepStatement(node.getAST(),
                    ++id, node.getExpression()));
        }
    }

    public void endVisit(ForStatement node) {
        final Expression guard = node.getExpression();
        replaceNode(guard, getSepStatement(guard.getAST(), ++id, guard));
    }


    public void endVisit(QualifiedName node) {

        if (node.getParent() instanceof QualifiedName) {
            return;
        }
            
        final Name qualifier = node.getQualifier();
        
        final IBinding qualifierBinding = qualifier.resolveBinding();
        
        if (qualifierBinding.getKind() == IBinding.PACKAGE) {
            return;
        }                   
        
        final IBinding simpleNameBinding = node.getName().resolveBinding();
        if (simpleNameBinding == null || 
                Modifier.isStatic(simpleNameBinding.getModifiers())) {           
            return;
        }
        
        if (qualifier.resolveTypeBinding() == null ||
                qualifier.resolveTypeBinding().isArray()) {
            return;               
        }
        
        types.add(qualifier.resolveTypeBinding());

        MethodInvocation inv = getSepStatement(qualifier.getAST(),
                ++id, qualifier);

        FieldAccess fa = node.getAST().newFieldAccess();

        fa.setName(node.getAST().newSimpleName(node.getName().toString()));
        fa.setExpression(inv);

        replaceNode(node, fa);
   }


    public void endVisit(WhileStatement node) {
        final Expression guard = node.getExpression();
        MethodInvocation inv = getSepStatement(guard.getAST(), ++id, guard);
        replaceNode(guard, inv);
    }

    private ExpressionStatement getSepStatement(AST ast, int id) {
        MethodInvocation methodInvocation = ast.newMethodInvocation();

        methodInvocation.setExpression(ast
                .newSimpleName(VisualDebugger.debugClass));
        methodInvocation.setName(ast.newSimpleName(VisualDebugger.sepName));

        NumberLiteral literal = ast.newNumberLiteral("" + id);
        methodInvocation.arguments().add(literal);
        ExpressionStatement expressionStatement = ast
                .newExpressionStatement(methodInvocation);
        return expressionStatement;
    }

    private MethodInvocation getSepStatement(AST ast, int id, Expression ex) {
        MethodInvocation methodInvocation = ast.newMethodInvocation();
        methodInvocation.setExpression(ast
                .newSimpleName(VisualDebugger.debugClass));
        // methodInvocation.setExpression(null);
        methodInvocation.setName(ast.newSimpleName(VisualDebugger.sepName));
        NumberLiteral literal = ast.newNumberLiteral("" + id);
        ASTNode ex2 = ASTNode.copySubtree(ast, ex);

        ASTParser parser = ASTParser.newParser(AST.JLS3);
        parser.setKind(ASTParser.K_EXPRESSION);
        parser.setSource(ex.toString().toCharArray()); // set source
        // parser.setResolveBindings(true); // we need bindings later on
        ex2 = (ASTNode.copySubtree(ast, (Expression) parser
                .createAST(null /* IProgressMonitor */)));
        // TODO !!!!!!!!!!!!!!!!!!!!!!!!

        methodInvocation.arguments().add(literal);
        methodInvocation.arguments().add((Expression) ex2);
      
        return methodInvocation;
    }

    public HashSet getTypes() {
        return types;
    }

    public boolean visit(ASTNode node) {        
        return true;
    }

    public boolean visit(Block node) {
        AST ast = node.getAST();
        for (int i = 0; i < node.statements().size(); i++) {
            id++;
            if (!(node.statements().get(i) instanceof SuperMethodInvocation)
                    && !(node.statements().get(i) instanceof ConstructorInvocation))
                node.statements().add(i, getSepStatement(ast, id));
            i++;
        }
        return true;
    }

}

