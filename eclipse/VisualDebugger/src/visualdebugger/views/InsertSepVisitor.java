package visualdebugger.views;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.HashSet;

import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Path;
import org.eclipse.jdt.core.dom.*;
import org.eclipse.jdt.core.dom.InfixExpression.Operator;
import org.eclipse.jdt.core.dom.rewrite.ASTRewrite;
import org.eclipse.jdt.core.dom.rewrite.ListRewrite;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.text.edits.MalformedTreeException;
import org.eclipse.text.edits.TextEdit;

import de.uka.ilkd.key.visualdebugger.VisualDebugger;

// TODO: Auto-generated Javadoc
/**
 * The Class InsertSepVisitor
 * 
 * This Class inserts Debug._sep(intlit) methods into the original sourcecode
 * 
 */
public class InsertSepVisitor extends ASTVisitor {

    /** The id. */
    private int id = 0;

    /** the CompilationUnit to be rewritten */
    private final CompilationUnit astRoot;

    private ASTRewrite rewrite;

    /**
     * Creates an instance of this visitor used to add breakpoints between each statement
     * and around expression that may implicitly trigger an unchecked exception.
     * @param astRoot the CompilationUnit to be rewritten
     */
    public InsertSepVisitor(CompilationUnit astRoot) {
        this.id = 0;
        this.astRoot = astRoot;
    }
    
    /**
     * Replace node.
     * 
     * @param oldNode the old node
     * @param newNode the new node
     */
    private void replaceNode(ASTNode oldNode, ASTNode newNode) {
        rewrite.replace(oldNode, newNode, null);        
    }

    
    /**
     * An array access might cause a NullPointer- or ArrayIndexOutOfBoundException therefore
     * we set a breakpoint around the access, i.e. <code>a[Debug.sep(id1, i)]</code>
     */
    public void endVisit(ArrayAccess node) {        
        Expression index = node.getIndex();
        replaceNode(index, getSepStatement(index.getAST(), ++id, index));
    }
    

    /**
     * Fields access may cause NullPointerException and need to be surrounded 
     * by a <code>Debug.sep(id, o).a</code>
     */
    public void endVisit(FieldAccess node) {
        final ITypeBinding expressionTypeBinding = node.getExpression()
                .resolveTypeBinding();
        if (expressionTypeBinding != null) {
            replaceNode(node.getExpression(), getSepStatement(node.getAST(),
                    ++id, node.getExpression()));
        } 
    }

    /**
     * Division-by-zero ArithmeticExceptions can occur when evaluating
     * the division or remainder infix operator. We take care of them here.     
     */
    public void endVisit(InfixExpression node) {
        if (node.getOperator() == Operator.DIVIDE || 
                node.getOperator() == Operator.REMAINDER) {
            replaceNode(node.getRightOperand(), 
                    getSepStatement(node.getAST(), ++id, node.getRightOperand()));
        }        
    }

    /**
     * Division-by-zero ArithmeticExceptions can occur when evaluating
     * the division or remainder composite assignment operator. 
     */
    public void endVisit(Assignment node) {
        if (node.getOperator() == Assignment.Operator.DIVIDE_ASSIGN || 
                node.getOperator() == Assignment.Operator.REMAINDER_ASSIGN) {
            replaceNode(node.getRightHandSide(), 
                    getSepStatement(node.getRightHandSide().getAST(), ++id, node.getRightHandSide()));
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
        replaceNode(guard, getSepStatement(guard.getAST(), ++id, guard));
        final Statement body = node.getBody();
        useBlocksInControlStatement(body);

    }

    /**
     * Ensures that existing then and else statements use blocks and their first statement 
     * is a breakpoint 
     */
    public void endVisit(IfStatement node) {
        final Statement thenStmnt = node.getThenStatement();
        useBlocksInControlStatement(thenStmnt);
        final Statement elseStmnt = node.getElseStatement();
        if (elseStmnt != null) {
            useBlocksInControlStatement(elseStmnt);
        }
    }

    
    /**
     * If the given Statement is not a Block then a block statement is created with the first 
     * statement being a <code>Debug.sep</code> statement and a copy of body as second statement.
     * @param body the Statement to be wrapped
     */
    private void useBlocksInControlStatement(final Statement body) {
        if (!(body instanceof Block)) {    
            final Block block = body.getAST().newBlock();
            id++;
            block.statements().add(getSepStatement(block.getAST(), id));
            block.statements().add(ASTNode.copySubtree(block.getAST(), body));
            rewrite.replace(body, block, null);            
        }
    }

    
    /**
     * The guard of a for statement is enclosed by a <code>Debug.sep</code>
     * statement. 
     * 
     * If the body of the loop is only a single statement and not a block, we have to enclose it
     * in a block and to add a <code>Debug.sep</code> statement as first statement of the body. 
     */
    public void endVisit(ForStatement node) {
        final Expression guard = node.getExpression();
        replaceNode(guard, getSepStatement(guard.getAST(), ++id, guard));
        final Statement body = node.getBody();
        useBlocksInControlStatement(body);
    }

    /**
     * At the processing stage when we access the AST a field access may be either represented
     * by a <code>FieldAccess</code> node or a <code>QualifiedName</code> node. The latter case 
     * is what we take care here.  
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

        if (qualifier.resolveTypeBinding() == null) {
            return;
        }

        Expression sep = getSepStatement(qualifier.getAST(), ++id,
                qualifier);

        FieldAccess fa = node.getAST().newFieldAccess();

        fa.setName(node.getAST().newSimpleName(node.getName().toString()));
        fa.setExpression(sep);

        replaceNode(node, fa);
    }

    /**
     * The guard of a while statement is enclosed by a <code>Debug.sep</code>
     * statement. 
     * 
     * If the body of the loop is only a single statement and not a block, we have to enclose it
     * in a block and to add a <code>Debug.sep</code> statement as first statement of the body. 
     */
    public void endVisit(WhileStatement node) {
        final Expression guard = node.getExpression();
        Expression sep = getSepStatement(guard.getAST(), ++id, guard);
        replaceNode(guard, sep);
        final Statement body = node.getBody();
        useBlocksInControlStatement(body);
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

        methodInvocation.setExpression(ast.newSimpleName(VisualDebugger.debugClass));
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
    private Expression getSepStatement(AST ast, int id, Expression ex) {        
        MethodInvocation methodInvocation = ast.newMethodInvocation();
        methodInvocation.setExpression(ast
                .newSimpleName(VisualDebugger.debugClass));
        // methodInvocation.setExpression(null);
        methodInvocation.setName(ast.newSimpleName(VisualDebugger.sepName));
        NumberLiteral literal = ast.newNumberLiteral("" + id);
       
        
        methodInvocation.arguments().add(literal);
        methodInvocation.arguments().add(ASTNode.copySubtree(methodInvocation.getAST(), ex));


        ITypeBinding binding = ex.resolveTypeBinding();
        
        if (binding != null && !binding.isPrimitive()) {
            // The sep statement has to be cast to the according reference type
            // Attention we derive here from Marcus master thesis where he created a method 
            // for each type in class Debug. But that approach does not work with visibility issues and breaks
            // as soon as non-public classes are involved. Instead the Debug class has only methods for
            // primitive types and one for java.lang.Object. 

            final CastExpression ce = ast.newCastExpression();
            ce.setExpression(methodInvocation);            
            final Type newType = getType(ast, binding);
            ce.setType(newType);            
            ParenthesizedExpression pe = ast.newParenthesizedExpression();
            pe.setExpression(ce);
            return pe;
        } else if (binding == null) {
            System.out.println("Warning: Could not resolve type of "+ex+" trying safe fallback.");            
        }        
        return methodInvocation;
    }

    private Type getType(AST ast, ITypeBinding bind) {
        if (bind.isPrimitive()) {
            return ast.newPrimitiveType(PrimitiveType.toCode(bind.getName()));
        } else if (bind.isArray()) {
            return ast.newArrayType(getType(ast, bind.getComponentType()));
        }        
        return ast.newSimpleType(ast.newName(bind.getQualifiedName()));
    }

    /**
     *  (non-Javadoc)
     * @see org.eclipse.jdt.core.dom.ASTVisitor#visit(org.eclipse.jdt.core.dom.Block)
     */
    public boolean visit(Block node) {      
        final ListRewrite listRewrite = rewrite.getListRewrite(node, Block.STATEMENTS_PROPERTY);
        // the index where to insert a statement breakpoint has to take care of the previously 
        // inserted sep statements
        int offset = 0;
        for (int i = 0, sz = node.statements().size(); i < sz; i++) {
            if (!(node.statements().get(i) instanceof SuperConstructorInvocation)
                    && !(node.statements().get(i) instanceof ConstructorInvocation)) {                
                id++;
                listRewrite.insertAt(getSepStatement(node.getAST(), id), i + offset, null);    
                offset++;
            }
        }
        return true;
    }

    /**
     * starts the insertion of breakpoint, i.e. <code>Debug.sep</code> statements.
     */
    public void start() {
        rewrite = ASTRewrite.create(astRoot.getAST());
        addImports();
        astRoot.accept(this);
    }
        
    public void finish(String prefix, IDocument document) throws MalformedTreeException, 
                                                                    BadLocationException, 
                                                                    IOException {
        IPath path = Path.fromOSString(prefix).append(astRoot.getJavaElement().getPath());
        File dirs = path.removeLastSegments(1).toFile();
        dirs.mkdirs();
        
        File compUnitFile = path.toFile();
        
        TextEdit edits = rewrite.rewriteAST(document, null);        

        edits.apply(document);

        compUnitFile.createNewFile();
        
        FileWriter fw = new FileWriter(compUnitFile);        
        try {
            fw.append(document.get());
        } finally {
            fw.close();
        }
    }

    /**
     * After the rewrite the source code contains references to the <code>Debug</code> 
     * class, therefore we need to import this class in the namespace of the CompilationUnit 
     * to be rewritten.
     */
    private void addImports() {       
        ListRewrite imports = rewrite.getListRewrite(astRoot, CompilationUnit.IMPORTS_PROPERTY);

        ImportDeclaration importDeclaration = astRoot.getAST().newImportDeclaration();

        importDeclaration.setName(astRoot.getAST().newSimpleName(VisualDebugger.debugPackage));
        importDeclaration.setOnDemand(true);

        imports.insertFirst(importDeclaration, null);                
    }

}
