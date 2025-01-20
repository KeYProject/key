/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.kit.transformation;

import recoder.CrossReferenceServiceConfiguration;
import recoder.java.NonTerminalProgramElement;
import recoder.java.Statement;
import recoder.java.StatementBlock;
import recoder.java.StatementContainer;
import recoder.java.declaration.LocalVariableDeclaration;
import recoder.kit.Conflict;
import recoder.kit.ProblemReport;
import recoder.kit.StatementKit;
import recoder.kit.TwoPassTransformation;
import recoder.list.generic.ASTArrayList;
import recoder.list.generic.ASTList;

/**
 * Syntactic transformation returning a mutable statement list that contains the given statement,
 * and creating a new {@linkrecoder.java.StatementBlock} if necessary. It is necessary to create a
 * new block, if {@link recoder.kit.StatementKit#getStatementMutableList}returns <CODE>null
 * </CODE>. This is the case if the statement container allows only a single statement and the given
 * statement is not inside a {@link recoder.java.StatementBlock}. If the statement has no parent, it
 * is wrapped into a new statement list.
 * <DL>
 * <DT>Added:
 * <DD>a new statement block, containing a cloned version of a statement if this is necessary and
 * the transformation is visible. The original or cloned statement is returned by the
 * {@link #getStatement()}method.
 * <DT>Removed:
 * <DD>the original statement wrapped by a block, in case this is necessary.
 * </DL>
 *
 * @author AL
 * @see recoder.kit.StatementKit#getStatementMutableList
 */
public class PrepareStatementList extends TwoPassTransformation {

    private final boolean isVisible;
    private Statement statement;
    private StatementBlock block;
    private ASTList<Statement> list;

    /**
     * Creates a new transformation object that wraps a statement with a new statement block if
     * necessary.
     *
     * @param sc the service configuration to use.
     * @param s a statement to be wrapped by a new statement block.
     */
    public PrepareStatementList(CrossReferenceServiceConfiguration sc, Statement s,
            boolean isVisible) {
        super(sc);
        if (s == null) {
            throw new IllegalArgumentException("Missing statement");
        }
        this.statement = s;
        this.isVisible = isVisible;
    }

    public boolean isVisible() {
        return isVisible;
    }

    /**
     * Returns a new {@link recoder.kit.transformation.PrepareStatementList.IllegalParentContext} if
     * the statement is not embedded in a statement container, otherwise {@link #NO_PROBLEM}if the
     * statement is a local variable declaration (which might potentially change program semantics),
     * otherwise {@link #EQUIVALENCE}.
     *
     * @return the problem report.
     */
    public ProblemReport analyze() {
        ProblemReport report = IDENTITY;
        StatementContainer con = statement.getStatementContainer();
        if (con == null) {
            list = new ASTArrayList<>(statement);
        } else {
            list = StatementKit.getStatementMutableList(statement);
            if (list == null) {
                NonTerminalProgramElement parent = statement.getASTParent();
                block = getProgramFactory().createStatementBlock();
                if (!(parent instanceof StatementContainer)) {
                    return new IllegalParentContext(parent);
                }
                if (statement instanceof LocalVariableDeclaration) {
                    report = NO_PROBLEM;
                } else {
                    report = EQUIVALENCE;
                }
            }
        }
        return setProblemReport(report);
    }

    /**
     * Clones the statement and replaces it with a new statement block containing the cloned tree.
     *
     * @see #analyze()
     */
    public void transform() {
        super.transform();
        if (block != null) {
            replace(statement, block);
            if (isVisible()) {
                statement = statement.deepClone();
            }
            attach(statement, block, 0);
            list = block.getBody();
        }
    }

    /**
     * Returns the new statement block after the transformation, if there had one to be inserted.
     * The block will contain the statement or a clone of the statement as sole child node.
     *
     * @return the new statement block replacing the given statement, or <CODE>
     * null</CODE> if there a new block was not necessary.
     * @see #getStatement()
     */
    public StatementBlock getBlock() {
        return block;
    }

    /**
     * @return the statement mutable list containing the given statement.
     */
    public ASTList<Statement> getStatementList() {
        return list;
    }

    /**
     * Returns the statement that has been wrapped. If this is a visible transformation and the
     * statement had to be wrapped, a clone of the initial argument is returned.
     *
     * @return the statement that has been wrapped, possibly a clone of the original statement.
     */
    public Statement getStatement() {
        return statement;
    }

    /**
     * Problem report indicating that a parent is not suited for a given child.
     */
    public static class IllegalParentContext extends Conflict {

        /**
         * serialization id
         */
        private static final long serialVersionUID = -1995165154877949565L;
        private final NonTerminalProgramElement parent;

        public IllegalParentContext(NonTerminalProgramElement parent) {
            this.parent = parent;
        }

        public NonTerminalProgramElement getParent() {
            return parent;
        }
    }

}
