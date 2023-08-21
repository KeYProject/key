/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.kit;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import recoder.ProgramFactory;
import recoder.abstraction.Type;
import recoder.abstraction.Variable;
import recoder.convenience.Format;
import recoder.convenience.Formats;
import recoder.convenience.ProgramElementWalker;
import recoder.java.*;
import recoder.java.declaration.*;
import recoder.java.reference.TypeReference;
import recoder.java.reference.VariableReference;
import recoder.java.statement.*;
import recoder.list.generic.ASTArrayList;
import recoder.list.generic.ASTList;
import recoder.service.ChangeHistory;
import recoder.service.CrossReferenceSourceInfo;
import recoder.service.SourceInfo;
import recoder.util.Debug;

public class StatementKit {

    private StatementKit() {
        super();
    }

    /**
     * Transformation returning a mutable statement list that contains the given statement, and
     * creating a new {@link recoder.java.StatementBlock}if necessary. It is necessary to create a
     * new block, if {@link #getStatementMutableList}returns <CODE>null</CODE>. This is the case if
     * the statement container allows only a single statement and the given statement is not inside
     * a {@link recoder.java.StatementBlock}. If the statement has no parent, it is wrapped into a
     * new statement list which then is returned.
     *
     * @param s a statement; may not be <CODE>null</CODE>.
     * @param ch the change history; may be <CODE>null</CODE>.
     * @return the mutable statement list that the given statement is part of; the list is contained
     *         in a new StatementBlock if necessary.
     * @see #getStatementMutableList
     * @see #wrapWithStatementBlock
     * @deprecated replaced by first class transformation PrepareStatementList
     */
    @Deprecated
    public static ASTList<Statement> prepareStatementMutableList(Statement s, ChangeHistory ch) {
        Debug.assertNonnull(s);
        StatementContainer con = s.getStatementContainer();
        if (con == null) {
            ASTList<Statement> result = new ASTArrayList<>();
            result.add(s);
            return result;
        }
        ASTList<Statement> result = getStatementMutableList(s);
        if (result == null) {
            result = wrapWithStatementBlock(s, ch).getBody();
        }
        return result;
    }

    /**
     * Query returning a mutable statement list that contains the given statement, if there is such
     * a list.
     * <UL>
     * <LI>If the statement container already features a statement mutable list, this list is
     * returned (e.g. {@link recoder.java.statement.Case}).</LI>
     * <LI>If the statement container is a {@link recoder.java.StatementBlock}, its list is returned
     * (except it is empty).</LI>
     * <LI>If the statement is the body of a {@link recoder.java.statement.LabeledStatement}, the
     * list for that labeled statement is returned instead.</LI>
     * </UL>
     *
     * @param s a statement; may not be <CODE>null</CODE>.
     * @return the mutable statement list that the given statement is part of, or <CODE>null</CODE>
     *         if there is none.
     */
    public static ASTList<Statement> getStatementMutableList(Statement s) {
        Debug.assertNonnull(s);
        StatementContainer con = s.getStatementContainer();
        if (con == null) {
            return null;
        }
        Statement body = null;
        if (con instanceof Statement) {
            if (con instanceof StatementBlock) {
                return ((StatementBlock) con).getBody();
            }
            if (con instanceof Branch) {
                if (con instanceof Then) {
                    body = ((Then) con).getBody();
                } else if (con instanceof Else) {
                    body = ((Else) con).getBody();
                } else if (con instanceof Case) {
                    // must not be null!
                    return ((Case) con).getBody();
                } else if (con instanceof Default) {
                    return ((Default) con).getBody();
                } else if (con instanceof Catch) {
                    body = ((Catch) con).getBody();
                } else if (con instanceof Finally) {
                    body = ((Finally) con).getBody();
                }
            } else if (con instanceof Try) {
                body = ((Try) con).getBody();
            } else if (con instanceof SynchronizedBlock) {
                body = ((SynchronizedBlock) con).getBody();
            } else if (con instanceof LabeledStatement) {
                return getStatementMutableList((LabeledStatement) con);
            }
        } else if (con instanceof MemberDeclaration) {
            if (con instanceof MethodDeclaration) {
                body = ((MethodDeclaration) con).getBody();
            } else if (con instanceof ClassInitializer) {
                body = ((ClassInitializer) con).getBody();
            }
        }
        if (body == null) {
            Debug.assertBoolean(true, "Could not handle container of statement "
                + Format.toString(Formats.ELEMENT_LONG, s));
        }
        if (body instanceof StatementBlock && body != s) {
            return ((StatementBlock) body).getBody();
        }
        return null;
    }

    /**
     * Transformation creating a new StatementBlock replacing the given statement and shifting it
     * inside. If the statement has no parent, it is put into the new statement block and no changes
     * are propagated. The new block is created even if the statement container already is a block.
     * The new block is replacing the old statement with valid parent link. This transformation is
     * safe if the statement is not an instance of
     * {@link recoder.java.declaration.LocalVariableDeclaration}containing a variable that is
     * actually referred.
     *
     * @param s a statement to be wrapped by a new statement block.
     * @param ch the change history; may be <CODE>null</CODE>.
     * @return the new statement block replacing <CODE>s</CODE>.
     * @deprecated
     */
    @Deprecated
    public static StatementBlock wrapWithStatementBlock(Statement s, ChangeHistory ch) {
        Debug.assertNonnull(s);
        StatementContainer con = s.getStatementContainer();
        StatementBlock block = s.getFactory().createStatementBlock();
        if (con != null) {
            con.replaceChild(s, block);
            if (ch != null) {
                ch.replaced(s, block);
            }
        }
        block.setBody(new ASTArrayList<>(1));
        block.getBody().add(s);
        block.makeParentRoleValid();
        return block;
    }

    /**
     * Query deciding if the given single statement can be wrapped inside a block without changing
     * program semantics. This is the case if the statement is not an instance of
     * {@link recoder.java.declaration.LocalVariableDeclaration}containing a variable that is
     * actually referred from outside.
     *
     * @param xr the cross referencer service used.
     * @param s a statement that might be wrapped.
     * @return <CODE>true</CODE> if wrapping the statement in a block would not change the program
     *         semantics, <CODE>false</CODE> otherwise.
     * @deprecated
     */
    @Deprecated
    public static boolean canSafelyWrapWithStatementBlock(CrossReferenceSourceInfo xr,
            Statement s) {
        Debug.assertNonnull(xr, s);
        if (s instanceof LocalVariableDeclaration) {
            LocalVariableDeclaration lvd = (LocalVariableDeclaration) s;
            List<? extends VariableSpecification> vsl = lvd.getVariables();
            for (int j = vsl.size() - 1; j >= 0; j -= 1) {
                Variable v = vsl.get(j);
                List<? extends VariableReference> vrl = xr.getReferences(v);
                for (int i = vrl.size() - 1; i >= 0; i -= 1) {
                    if (!MiscKit.contains(lvd, vrl.get(i))) {
                        return false;
                    }
                }
            }
        }
        return true;
    }

    /**
     * Transformation that ensures that the given return or throw statement can be safely prepended
     * by other statements. If the statement contains an expression that contains statements (side
     * effects possible), the expression is replaced by a variable reference to a new temporary
     * variable initialized by the former return value. If necessary, a new statement block is
     * created wrapping the return or throw statement.
     *
     * @param ch the change history service (may be <CODE>null</CODE>).
     * @param si the source info service.
     * @param returnOrThrow a return or throw statement.
     * @deprecated will become a first class transformation
     */
    @Deprecated
    public static void preparePrepend(ChangeHistory ch, SourceInfo si,
            ExpressionJumpStatement returnOrThrow) {
        Debug.assertNonnull(si, returnOrThrow);
        List<Statement> destination = prepareStatementMutableList(returnOrThrow, ch);
        if (returnOrThrow.getExpressionCount() == 0) {
            return;
        }
        Expression expr = returnOrThrow.getExpressionAt(0);
        if (!ExpressionKit.containsStatements(expr)) {
            return;
        }
        ProgramFactory f = returnOrThrow.getFactory();
        Type type = si.getType(expr);
        String vname =
            VariableKit.getNewVariableName(si, type, MiscKit.getScopeDefiningElement(expr));
        TypeReference tref = TypeKit.createTypeReference(si, type, expr);
        LocalVariableDeclaration lvd =
            f.createLocalVariableDeclaration(tref, f.createIdentifier(vname));
        lvd.getVariables().get(0).setInitializer(expr);
        lvd.makeAllParentRolesValid();
        VariableReference vref = f.createVariableReference(f.createIdentifier(vname));
        returnOrThrow.replaceChild(expr, vref);
        if (ch != null) {
            ch.replaced(expr, vref);
        }
        StatementContainer destParent = returnOrThrow.getStatementContainer();
        int idx;
        for (idx = 0; destination.get(idx) != returnOrThrow; idx += 1) {
            // logic contained in loop control
        }
        destination.add(idx, lvd);
        lvd.setStatementContainer(destParent); // manual parent link validation
        // alternatively: destParent.makeParentRoleValid()
        if (ch != null) {
            ch.attached(lvd);
        }
    }

    /**
     * Checks if the specified statement is reachable as defined in the static language semantics.
     *
     * @param s a statement.
     * @param si the SourceInfo service to use.
     * @return <CODE>true</CODE> if the statement is reachable, <CODE>false
     * </CODE> otherwise.
     * @since 0.71
     */
    public static boolean isReachable(Statement s, SourceInfo si) {
        MemberDeclaration member = MiscKit.getParentMemberDeclaration(s);
        ControlFlowWalker w = new ControlFlowWalker(member, si);
        while (w.next()) {
            if (w.getStatement() == s) {
                return true;
            }
        }
        return false;
    }

    /**
     * Checks if the end of the specified statement block is reachable as defined in the static
     * language semantics.
     *
     * @param block a statement block.
     * @param si the SourceInfo service to use.
     * @return <CODE>true</CODE> if the end of the block is reachable, <CODE>
     * false</CODE> otherwise.
     * @since 0.71
     */
    public static boolean hasReachableEnd(StatementBlock block, SourceInfo si) {
        List<Statement> body = block.getBody();
        if (body == null || body.isEmpty()) {
            return true;
        }
        Statement dummyExit = block.getFactory().createEmptyStatement();
        body.add(dummyExit);
        dummyExit.setStatementContainer(block);
        boolean result = isReachable(dummyExit, si);
        body.remove(body.size() - 1);
        return result;
    }

    /**
     * Syntactic query locating the label addressed by the specified labeled break or continue
     * statement.
     *
     * @param s a labeled jump statement.
     * @return the corresponding labeled statement, or <CODE>null</CODE> if there is none.
     * @since 0.71
     */
    public static LabeledStatement getCorrespondingLabel(LabelJumpStatement s) {
        // must be defined before and outward an enclosing loop or block
        String idText = s.getIdentifier().getText();
        NonTerminalProgramElement parent = s.getASTParent();
        while (parent != null) {
            if (parent instanceof LabeledStatement) {
                LabeledStatement lstat = (LabeledStatement) parent;
                if (idText.equals(lstat.getIdentifier().getText())) {
                    return lstat;
                }
            }
            parent = parent.getASTParent();
        }
        return null;
    }

    /**
     * For a method declaration or class initializer, returns a list of block exits, such as return
     * or throw statements, and the body if its exit is reachable. For other members, returns an
     * empty list.
     *
     * @param m a member declaration.
     * @param si the SourceInfo service to use.
     * @return a list of statements that finish the member's body after execution.
     * @since 0.72
     */
    public static List<Statement> getExits(MemberDeclaration mdecl, SourceInfo si) {
        Debug.assertNonnull(mdecl, si);
        List<Statement> result = new ArrayList<>();
        StatementBlock body = null;
        if (mdecl instanceof MethodDeclaration) {
            body = ((MethodDeclaration) mdecl).getBody();
        } else if (mdecl instanceof ClassInitializer) {
            body = ((ClassInitializer) mdecl).getBody();
        }
        if (body == null) {
            return new ArrayList<>(0);
        }
        Statement dummyExit = body.getFactory().createEmptyStatement();
        int s = (body.getBody() == null) ? 0 : body.getBody().size();
        Transformation.doAttach(dummyExit, body, s);
        ControlFlowWalker w = new ControlFlowWalker(mdecl, si);
        while (w.next()) {
            ProgramElement p = w.getProgramElement();
            if (p == dummyExit) {
                result.add(body);
            } else if (p instanceof ExpressionJumpStatement) {
                result.add((Statement) p);
            }
        }
        Transformation.doDetach(dummyExit);
        return result;
    }

    /**
     * This walker performs a depth first search and reports the reachable statements in the body of
     * the given member. Only non-abstract method declarations, constructor declarations, and class
     * initializers can report statements. This implementation follows the static rules of the Java
     * language specification and evaluates boolean conditions as Java compile-time constants only.
     * No intra-procedural analysis is performed and throw statements are not mapped to
     * corresponding catch clauses. <BR>
     * To create a control flow graph, use the walker and query the succeeding statements for each
     * reported statement.
     *
     * @since 0.71
     */
    public static class ControlFlowWalker implements ProgramElementWalker {

        private final SourceInfo si;
        private final Set<Statement> reached;
        private final List<Statement> stack;
        private Statement current;
        private List<Statement> successors;

        // either a method declaration or class initializer
        public ControlFlowWalker(MemberDeclaration parent, SourceInfo si) {
            if (si == null || parent == null) {
                throw new IllegalArgumentException();
            }
            this.si = si;
            reached = new HashSet<>();
            stack = new ArrayList<>();
            if (parent instanceof MethodDeclaration) {
                StatementBlock body = ((MethodDeclaration) parent).getBody();
                if (body != null) {
                    stack.add(body);
                }
            } else if (parent instanceof ClassInitializer) {
                StatementBlock body = ((ClassInitializer) parent).getBody();
                if (body != null) {
                    stack.add(body);
                }
            }
        }

        public boolean next() {
            int size = stack.size();
            if (size == 0) {
                current = null;
                successors = null;
                return false;
            }
            current = stack.get(size - 1);
            reached.add(current);
            stack.remove(size - 1);
            successors = si.getSucceedingStatements(current);
            for (Statement f : successors) {
                if (f != SourceInfo.METHOD_EXIT && !reached.contains(f)) {
                    stack.add(f);
                }
            }
            return true;
        }

        public ProgramElement getProgramElement() {
            return current;
        }

        public Statement getStatement() {
            return current;
        }

        /**
         * Returns the successors of the current statement.
         *
         * @return the list of successors of the current statement, or <CODE>
         * null</CODE> if the current statement is <CODE>null</CODE>.
         * @see #getStatement
         * @see recoder.service.SourceInfo#getSucceedingStatements
         */
        public List<Statement> getSucceedingStatements() {
            return successors;
        }

        /**
         * Returns <CODE>true</CODE> if the specified statement has been found reachable already.
         * The returned value remains valid after the iteration has finished.
         */
        public boolean isReachable(Statement s) {
            return reached.contains(s);
        }
    }

}
