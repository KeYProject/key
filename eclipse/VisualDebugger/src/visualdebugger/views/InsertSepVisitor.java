package visualdebugger.views;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;

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

/**
 * 
 * Inserts breakpoints into a given compilation unit and writes the altered unit out at
 * a specified place. Breakpoints are represented by <code>Debug.sep</code> method calls
 * and inserted before each statement (except this- and super constructor invocations). 
 * In the following we use breakpoint and sep-statement to denote the same concept. 
 * 
 * Each breakpoint has an associated unique id modelled as an integer literal.
 * 
 * The <code>Debug</code> class contains several kinds of <code>sep</code> method declarations, 
 * as sometimes it is necessary to put an expression breakpoint around guards, field- or array 
 * accesses as those may cause runtime exceptions. 
 * 
 * The following <code>sep</code> methods are used:
 * <ul>
 * <li><code>void sep(int id)</code> for statement breakpoints</li>
 * <li><code>(long|int|short|byte|char) sep(int id, (long|int|short|byte|char) expr)</code> in case
 * an expression breakpoint needs to be set at a primitive typed expression <code>expr</code> e.g.
 * <code>Debug.sep(id,expr)</code> the <code>sep</code> methods implementation simply returns <code>expr</code></li> 
 * <li><code>java.lang.Object sep(int id, java.lang.Object)</code> in case of expression breakpoints for reference
 * typed expressions, those are wrapped as in <code>((T)Debug.sep(id,expr))</code> where <code>T</code> is the static 
 * type of <code>expr</code></li>
 * </ul>
 *  
 *  The visitor processes the given AST when invoking method {@link #start()}. The rewrite is performed by a 
 *  succeeding call to {@link #finish(String, IDocument)}.
 */
public class InsertSepVisitor extends ASTVisitor {

    /** The id. */
    private int id = 0;

    /** the CompilationUnit to be rewritten */
    private final CompilationUnit cunit;

    /** the AST associated with the root */
    private final AST ast;
    
    private ASTRewrite rewrite;

    /**
     * Creates an instance of this visitor used to add breakpoints between each statement
     * and around expression that may implicitly trigger an unchecked exception.
     * @param astRoot the CompilationUnit to be rewritten
     */
    public InsertSepVisitor(CompilationUnit astRoot) {
        this.id = 0;
        this.cunit = astRoot;
        this.ast = astRoot.getAST();
    }
    
    /**
     * An array access might cause a NullPointer- or ArrayIndexOutOfBoundException therefore
     * we set a breakpoint around the access, i.e. <code>a[Debug.sep(id1, i)]</code>
     */
    public void endVisit(ArrayAccess node) {        
        Expression index = node.getIndex();
        rewrite.replace(index, getSepStatement(++id, index), null);
    }
    

    /**
     * Fields access may cause NullPointerException and need to be surrounded 
     * by a <code>Debug.sep(id, o).a</code>
     */
    public void endVisit(FieldAccess node) {
        final ITypeBinding expressionTypeBinding = node.getExpression()
                .resolveTypeBinding();
        if (expressionTypeBinding != null) {
            rewrite.replace(node.getExpression(), getSepStatement(++id,
            node.getExpression()), null);
        } 
    }

    /**
     * Division-by-zero ArithmeticExceptions can occur when evaluating
     * the division or remainder infix operator. We take care of them here.     
     */
    public void endVisit(InfixExpression node) {
        if (node.getOperator() == Operator.DIVIDE || 
                node.getOperator() == Operator.REMAINDER) {
            rewrite.replace(node.getRightOperand(), getSepStatement(++id, node.getRightOperand()), null);
        }        
    }

    /**
     * Division-by-zero ArithmeticExceptions can occur when evaluating
     * the division or remainder composite assignment operator. 
     */
    public void endVisit(Assignment node) {
        if (node.getOperator() == Assignment.Operator.DIVIDE_ASSIGN || 
                node.getOperator() == Assignment.Operator.REMAINDER_ASSIGN) {
            rewrite.replace(node.getRightHandSide(), getSepStatement(++id, node.getRightHandSide()), null);
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
        rewrite.replace(guard, getSepStatement(++id, guard), null);
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
            block.statements().add(getSepStatement(id));
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
        rewrite.replace(guard, getSepStatement(++id, guard), null);
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

        Expression sep = getSepStatement(++id, qualifier);

        FieldAccess fa = node.getAST().newFieldAccess();

        fa.setName(node.getAST().newSimpleName(node.getName().toString()));
        fa.setExpression(sep);

        rewrite.replace(node, fa, null);
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
        Expression sep = getSepStatement(++id, guard);
        rewrite.replace(guard, sep, null);
        final Statement body = node.getBody();
        useBlocksInControlStatement(body);
    }

    /**
     * Gets the sep statement.
     * @param id the id
     * 
     * @return the sep statement
     */
    private ExpressionStatement getSepStatement(int id) {
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
     * @param id the id
     * @param ex the ex
     * 
     * @return the sep statement
     */
    private Expression getSepStatement(int id, Expression ex) {        
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
            final Type newType = getType(binding);
            ce.setType(newType);            
            ParenthesizedExpression pe = ast.newParenthesizedExpression();
            pe.setExpression(ce);
            return pe;
        } else if (binding == null) {
            System.out.println("Warning: Could not resolve type of "+ex+" trying safe fallback.");            
        }        
        return methodInvocation;
    }

    /**
     * determines the Type object for the given type binding
     * @param bind
     * @return
     */
    private Type getType(ITypeBinding bind) {
        if (bind.isPrimitive()) {
            return ast.newPrimitiveType(PrimitiveType.toCode(bind.getName()));
        } else if (bind.isArray()) {
            return ast.newArrayType(getType(bind.getComponentType()));
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
                listRewrite.insertAt(getSepStatement(id), i + offset, null);    
                offset++;
            }
        }
        return true;
    }

    /**
     * starts the insertion of breakpoint, i.e. <code>Debug.sep</code> statements.
     */
    public void start() {
        rewrite = ASTRewrite.create(ast);
        addImports();
        cunit.accept(this);
    }
        
    /**
     * applies the changes to the given document and writes the result to 
     * <code>prefix + unit.getJavaElement().getPath()</code>
     * @param prefix String describing root directory where to start writing the document
     * @param document the IDocument where to apply the edits
     * @throws MalformedTreeException thrown if edits constructed an invalid AST 
     * @throws BadLocationException if some location information is wrong
     * @throws IOException if the file where to write could not be created/opened for some reasons.
     */
    public void finish(String prefix, IDocument document) throws MalformedTreeException, 
                                                                    BadLocationException, 
                                                                    IOException {
        IPath path = Path.fromOSString(prefix).append(cunit.getJavaElement().getPath());
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
        ListRewrite imports = rewrite.getListRewrite(cunit, CompilationUnit.IMPORTS_PROPERTY);

        ImportDeclaration importDeclaration = ast.newImportDeclaration();

        importDeclaration.setName(ast.newSimpleName(VisualDebugger.debugPackage));
        importDeclaration.setOnDemand(true);

        imports.insertFirst(importDeclaration, null);                
    }

}
