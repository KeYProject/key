/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.metaconstruct;

import java.util.ArrayList;
import java.util.List;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.KeYJavaASTFactory;
import de.uka.ilkd.key.java.Label;
import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.expression.operator.Equals;
import de.uka.ilkd.key.java.expression.operator.New;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.statement.*;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.VariableNamer;
import de.uka.ilkd.key.logic.op.ProgramSV;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/**
 * This class is used to perform program transformations needed for the symbolic execution of a
 * switch-case statement.
 */
public class SwitchToIf extends ProgramTransformer {

    private boolean noNewBreak = true;

    /**
     * creates a switch-to-if ProgramTransformer
     *
     * @param _switch the Statement contained by the meta construct
     */
    public SwitchToIf(SchemaVariable _switch) {
        super("switch-to-if", (ProgramSV) _switch);
    }

    @Override
    public ProgramElement[] transform(ProgramElement pe, Services services,
            SVInstantiations insts) {
        Switch sw = (Switch) pe;

        VariableNamer varNamer = services.getVariableNamer();

        Label l = varNamer.getTemporaryNameProposal("_l");
        Break newBreak = KeYJavaASTFactory.breakStatement(l);

        ProgramElementName name = varNamer.getTemporaryNameProposal("_var");

        final ExecutionContext ec = insts.getExecutionContext();
        ProgramVariable exV =
            KeYJavaASTFactory.localVariable(name, sw.getExpression().getKeYJavaType(services, ec));
        Statement s =
            KeYJavaASTFactory.declare(name, sw.getExpression().getKeYJavaType(services, ec));

        sw = changeBreaks(sw, newBreak);
        Statement currentBlock = null;
        for (int i = sw.getBranchCount() - 1; 0 <= i; i--) {
            if (sw.getBranchAt(i) instanceof Default) {
                currentBlock = collectStatements(sw, i);
            }
        }
        for (int i = sw.getBranchCount() - 1; 0 <= i; i--) {
            if (sw.getBranchAt(i) instanceof Case) {
                Equals guard = KeYJavaASTFactory.equalsOperator(exV,
                    ((Case) sw.getBranchAt(i)).getExpression());
                StatementBlock caseBlock = collectStatements(sw, i);
                // Avoid creating a Else(null) block
                if (currentBlock != null) {
                    currentBlock = KeYJavaASTFactory.ifElse(guard, caseBlock, currentBlock);
                } else {
                    currentBlock = KeYJavaASTFactory.ifThen(guard, caseBlock);
                }
            }
        }
        // mulbrich: Added additional null check for enum constants
        if (!(sw.getExpression().getKeYJavaType(services, ec)
                .getJavaType() instanceof PrimitiveType)) {
            currentBlock = mkIfNullCheck(services, exV, currentBlock);
        }

        StatementBlock result;
        if (currentBlock != null) {
            result = KeYJavaASTFactory.block(s, KeYJavaASTFactory.assign(exV, sw.getExpression()),
                currentBlock);
        } else {
            // empty switch of primitive type, the expression can still have side-effects
            result = KeYJavaASTFactory.block(s, KeYJavaASTFactory.assign(exV, sw.getExpression()));
        }
        if (noNewBreak) {
            return new ProgramElement[] { result };
        } else {
            return new ProgramElement[] {
                KeYJavaASTFactory.labeledStatement(l, result, PositionInfo.UNDEFINED) };
        }
    }

    /**
     * return a check of the kind
     * <code>if(v == null) throw new NullPointerException(); else elseBlock</code>
     *
     * @return an if-statement that performs a null check
     */

    private If mkIfNullCheck(Services services, ProgramVariable var, Statement elseBlock) {
        final New exception = KeYJavaASTFactory.newOperator(
            services.getJavaInfo().getKeYJavaType("java.lang.NullPointerException"));
        Throw t = KeYJavaASTFactory.throwClause(exception);

        final Expression cnd = KeYJavaASTFactory.equalsNullOperator(var);

        // Avoid creating a Else(null) block
        if (elseBlock != null) {
            // for some reason the Statement variant is declared to return a Statement
            return (If) KeYJavaASTFactory.ifElse(cnd, t, elseBlock);
        } else {
            return KeYJavaASTFactory.ifThen(cnd, t);
        }
    }

    /**
     * Replaces all breaks in <code>sw</code>, whose target is sw, with <code>b</code>
     */
    private Switch changeBreaks(Switch sw, Break b) {
        int n = sw.getBranchCount();
        Branch[] branches = new Branch[n];
        for (int i = 0; i < n; i++) {
            branches[i] = (Branch) recChangeBreaks(sw.getBranchAt(i), b);
        }
        return KeYJavaASTFactory.switchBlock(sw.getExpression(), branches);
    }

    private ProgramElement recChangeBreaks(ProgramElement p, Break b) {
        if (p == null) {
            return null;
        }
        if (p instanceof Break && ((Break) p).getLabel() == null) {
            noNewBreak = false;
            return b;
        }
        if (p instanceof Branch) {
            Statement[] s = new Statement[((Branch) p).getStatementCount()];
            for (int i = 0; i < ((Branch) p).getStatementCount(); i++) {
                s[i] = (Statement) recChangeBreaks(((Branch) p).getStatementAt(i), b);
            }
            if (p instanceof Case) {
                return KeYJavaASTFactory.caseBlock(((Case) p).getExpression(), s);
            }
            if (p instanceof Default) {
                return KeYJavaASTFactory.defaultBlock(s);
            }
            if (p instanceof Catch) {
                return KeYJavaASTFactory.catchClause(((Catch) p).getParameterDeclaration(), s);
            }
            if (p instanceof Finally) {
                return KeYJavaASTFactory.finallyBlock(s);
            }
            if (p instanceof Then) {
                return KeYJavaASTFactory.thenBlock(s);
            }
            if (p instanceof Else) {
                return KeYJavaASTFactory.elseBlock(s);
            }
        }
        if (p instanceof If) {
            return KeYJavaASTFactory.ifElse(((If) p).getExpression(),
                (Then) recChangeBreaks(((If) p).getThen(), b),
                (Else) recChangeBreaks(((If) p).getElse(), b));
        }
        if (p instanceof StatementBlock) {
            Statement[] s = new Statement[((StatementBlock) p).getStatementCount()];
            for (int i = 0; i < ((StatementBlock) p).getStatementCount(); i++) {
                s[i] = (Statement) recChangeBreaks(((StatementBlock) p).getStatementAt(i), b);
            }
            return KeYJavaASTFactory.block(s);
        }
        if (p instanceof Try) {
            int n = ((Try) p).getBranchCount();
            Branch[] branches = new Branch[n];
            for (int i = 0; i < n; i++) {
                branches[i] = (Branch) recChangeBreaks(((Try) p).getBranchAt(i), b);
            }
            return KeYJavaASTFactory
                    .tryBlock((StatementBlock) recChangeBreaks(((Try) p).getBody(), b), branches);
        }
        return p;
    }

    /**
     * Collects the Statements in a switch statement from branch <code>count</code> downward.
     *
     * @param s the switch statement.
     * @param count the branch where the collecting of statements starts.
     */
    private StatementBlock collectStatements(Switch s, int count) {
        List<Statement> stats = new ArrayList<>();
        outer: for (int i = count; i < s.getBranchCount(); i++) {
            for (int j = 0; j < s.getBranchAt(i).getStatementCount(); j++) {
                Statement statement = s.getBranchAt(i).getStatementAt(j);
                stats.add(statement);
                if (statement instanceof JumpStatement) {
                    // unconditional jump to outside the case (?)
                    break outer;
                }
            }
        }
        return KeYJavaASTFactory.block(stats);
    }

}
