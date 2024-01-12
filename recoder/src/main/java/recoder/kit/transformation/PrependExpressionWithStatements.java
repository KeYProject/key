/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.kit.transformation;

import recoder.CrossReferenceServiceConfiguration;
import recoder.java.Expression;
import recoder.java.ProgramElement;
import recoder.java.Statement;
import recoder.java.StatementContainer;
import recoder.kit.Problem;
import recoder.kit.ProblemReport;
import recoder.kit.TwoPassTransformation;
import recoder.list.generic.ASTArrayList;
import recoder.list.generic.ASTList;
import recoder.service.ChangeHistory;

/**
 * Transformation that prepends a given expression (such as a method or variable reference) with a
 * statement or a list of statements.
 *
 * @author AL
 */
public class PrependExpressionWithStatements extends TwoPassTransformation {

    private final Expression expression;

    private final ASTList<Statement> statements;

    private ShiftPreceedingStatementExpressions shifter;

    /**
     * Creates a new transformation object that inserts the given statements such that no state
     * changes take place between the statements and the evaluation of the expression.
     *
     * @param sc the service configuration to use.
     * @param x the expression that shall be prepended.
     * @param statements the statements to prepend.
     */
    public PrependExpressionWithStatements(CrossReferenceServiceConfiguration sc, Expression x,
            ASTList<Statement> statements) {
        super(sc);
        if (x == null) {
            throw new IllegalArgumentException("Missing expression");
        }
        if (statements == null) {
            throw new IllegalArgumentException("Missing statements");
        }
        this.expression = x;
        this.statements = statements;
    }

    /**
     * Creates a new transformation object that inserts the given statement such that no state
     * changes take place between the statement and the evaluation of the expression.
     *
     * @param sc the service configuration to use.
     * @param x the expression that shall be prepended.
     * @param statement the statement to prepend.
     */
    public PrependExpressionWithStatements(CrossReferenceServiceConfiguration sc, Expression x,
            Statement statement) {
        this(sc, x, new ASTArrayList<>(statement));
    }

    /**
     * @return the problem report, may be {@link recoder.kit.Transformation#IDENTITY}, or
     *         {@link recoder.kit.Transformation#EQUIVALENCE}.
     */
    public ProblemReport analyze() {
        if (statements.isEmpty()) {
            return setProblemReport(IDENTITY);
        }
        shifter = new ShiftPreceedingStatementExpressions(getServiceConfiguration(), expression);
        ProblemReport report = shifter.analyze();
        if (report instanceof Problem) {
            return setProblemReport(report);
        }
        if (report == IDENTITY) {
            Statement parent = (Statement) shifter.getTopMostParent();
            StatementContainer grandpa = parent.getStatementContainer();
            int i = 0;
            for (int s = grandpa.getStatementCount(); i < s; i += 1) {
                if (grandpa.getStatementAt(i) == parent) {
                    break;
                }
            }
            int j = statements.size();
            if (i >= j) {
                for (--j, --i; j >= 0; --j, --i) {
                    if (!ProgramElement.STRUCTURAL_EQUALITY.equals(statements.get(j),
                        grandpa.getStatementAt(i))) {
                        break;
                    }
                }
                if (j < 0) {
                    return setProblemReport(report);
                }
            }
        }
        return setProblemReport(NO_PROBLEM);
    }

    /**
     * @throws IllegalStateException if the analysis has not been called.
     * @see #analyze()
     * @see recoder.kit.transformation.ShiftPreceedingStatementExpressions
     * @see recoder.kit.transformation.PrepareStatementList
     */
    public void transform() {
        super.transform();
        shifter.transform();
        Statement statement = shifter.getEnclosingStatement();
        // this is a syntactic transformation!
        PrepareStatementList preparer =
            new PrepareStatementList(getServiceConfiguration(), statement, true);
        preparer.execute();
        ASTList<Statement> body = preparer.getStatementList();
        // the statement might have been cloned
        statement = preparer.getStatement();
        int position = body.indexOf(statement);
        body.addAll(position, statements);
        ChangeHistory ch = getChangeHistory();
        StatementContainer parent = statement.getStatementContainer();
        for (Statement s : statements) {
            s.setStatementContainer(parent);
            if (isVisible()) {
                ch.attached(s);
            }
        }
    }
}
