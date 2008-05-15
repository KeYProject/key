package visualdebugger.views;

import java.util.HashSet;
import java.util.List;

import org.eclipse.jdt.core.dom.*;
import org.eclipse.jdt.core.dom.InfixExpression.Operator;

import de.uka.ilkd.key.visualdebugger.VisualDebugger;

// TODO: Auto-generated Javadoc
/**
 * The Class InsertSepVisitor
 * 
 * This Class inserts Debug._sep(intlit) methods into the original sourcecode
 * 
 */
public class InsertSepVisitor extends ASTVisitor {

    /**
     * Replace node.
     * 
     * @param oldNode the old node
     * @param newNode the new node
     */
    private void replaceNode(ASTNode oldNode, ASTNode newNode) {

        ASTNode parent = oldNode.getParent();
        StructuralPropertyDescriptor location = oldNode.getLocationInParent();

        if (location.isChildProperty()) {

            parent.setStructuralProperty(location, newNode);

        } else if (location.isChildListProperty()) {

            List<ASTNode> list = (List<ASTNode>) parent.getStructuralProperty(location);
            int index = list.indexOf(oldNode);
            list.set(index, newNode);
        }
    }

    /** The id. */
    private int id = 0;

    /** The types. */
    private final HashSet<ITypeBinding> types = new HashSet<ITypeBinding>();

    
    /**
     * An array access might cause a NullPointer- or ArrayIndexOutOfBoundException therefore
     * we set a breakpoint around the access, i.e. <code>a[Debug.sep(id1, i)]</code>
     */
    public void endVisit(ArrayAccess node) {        
        Expression index = node.getIndex();
        MethodInvocation indexSep = getSepStatement(index.getAST(), ++id, index);
        replaceNode(index, indexSep);
    }

    /* (non-Javadoc)
     * @see org.eclipse.jdt.core.dom.ASTVisitor#endVisit(org.eclipse.jdt.core.dom.FieldAccess)
     */
    public void endVisit(FieldAccess node) {
        final ITypeBinding expressionTypeBinding = node.getExpression()
                .resolveTypeBinding();
        if (expressionTypeBinding != null) {

            types.add(expressionTypeBinding);

            replaceNode(node.getExpression(), getSepStatement(node.getAST(),
                    ++id, node.getExpression()));
        }
    }

    public void endVisit(InfixExpression node) {
        if (node.getOperator() == Operator.DIVIDE) {
            replaceNode(node.getRightOperand(), 
                    getSepStatement(node.getAST(), ++id, node.getRightOperand()));
        }        
    }
    
    /* (non-Javadoc)
     * @see org.eclipse.jdt.core.dom.ASTVisitor#endVisit(org.eclipse.jdt.core.dom.ForStatement)
     */
    public void endVisit(ForStatement node) {
        final Expression guard = node.getExpression();
        replaceNode(guard, getSepStatement(guard.getAST(), ++id, guard));
    }

    /* (non-Javadoc)
     * @see org.eclipse.jdt.core.dom.ASTVisitor#endVisit(org.eclipse.jdt.core.dom.QualifiedName)
     */
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
        if (simpleNameBinding == null
                || Modifier.isStatic(simpleNameBinding.getModifiers())) {
            return;
        }

        if (qualifier.resolveTypeBinding() == null
                || qualifier.resolveTypeBinding().isArray()) {
            return;
        }

        types.add(qualifier.resolveTypeBinding());

        MethodInvocation inv = getSepStatement(qualifier.getAST(), ++id,
                qualifier);

        FieldAccess fa = node.getAST().newFieldAccess();

        fa.setName(node.getAST().newSimpleName(node.getName().toString()));
        fa.setExpression(inv);

        replaceNode(node, fa);
    }

    /* (non-Javadoc)
     * @see org.eclipse.jdt.core.dom.ASTVisitor#endVisit(org.eclipse.jdt.core.dom.WhileStatement)
     */
    public void endVisit(WhileStatement node) {
        final Expression guard = node.getExpression();
        MethodInvocation inv = getSepStatement(guard.getAST(), ++id, guard);
        replaceNode(guard, inv);
    }

    /**
     * Gets the sep statement.
     * 
     * @param ast the ast
     * @param id the id
     * 
     * @return the sep statement
     */
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

    /**
     * Gets the sep statement.
     * 
     * @param ast the ast
     * @param id the id
     * @param ex the ex
     * 
     * @return the sep statement
     */
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

    /**
     * Gets the types.
     * 
     * @return the types
     */
    public HashSet<ITypeBinding> getTypes() {
        return types;
    }

    /**
     * Visit.
     * 
     * @param node the node
     * 
     * @return true, if successful
     */
    public boolean visit(ASTNode node) {
        return true;
    }

    /* (non-Javadoc)
     * @see org.eclipse.jdt.core.dom.ASTVisitor#visit(org.eclipse.jdt.core.dom.Block)
     */
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
