/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.rule.metaconstruct;

import java.util.ArrayList;
import java.util.List;
import java.util.Objects;

import de.uka.ilkd.key.java.KeYJavaASTFactory;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.Label;
import de.uka.ilkd.key.java.ast.PositionInfo;
import de.uka.ilkd.key.java.ast.ProgramElement;
import de.uka.ilkd.key.java.ast.Statement;
import de.uka.ilkd.key.java.ast.StatementBlock;
import de.uka.ilkd.key.java.ast.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.ast.expression.Expression;
import de.uka.ilkd.key.java.ast.expression.operator.BinaryOperator;
import de.uka.ilkd.key.java.ast.expression.operator.New;
import de.uka.ilkd.key.java.ast.reference.ExecutionContext;
import de.uka.ilkd.key.java.ast.statement.*;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.VariableNamer;
import de.uka.ilkd.key.logic.op.ProgramSV;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

import org.key_project.logic.op.sv.SchemaVariable;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * This class is used to perform program transformations needed for the symbolic execution of a
 * switch-case statement.
 */
@NullMarked
public class SwitchToIf extends ProgramTransformer {


    /**
     * creates a switch-to-if ProgramTransformer
     *
     * @param _switch
     *        the Statement contained by the meta construct
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
        // a well-formed switch always has a discriminator expression with a registered type
        final var switchExpr = Objects.requireNonNull(sw.getExpression(),
            "no expression for switch-to-if");
        final var switchType = Objects.requireNonNull(
            switchExpr.getKeYJavaType(services, ec),
            "no KeYJavaType for switch expression");
        ProgramVariable exV = KeYJavaASTFactory.localVariable(name, switchType);
        Statement s = KeYJavaASTFactory.declare(name, switchType);

        final var changeBreakResult = changeBreaks(sw, newBreak, true);
        sw = (Switch) changeBreakResult.result;
        Statement currentBlock = null;
        for (int i = sw.getBranchCount() - 1; 0 <= i; i--) {
            if (sw.getBranchAt(i) instanceof Default) {
                currentBlock = collectStatements(sw, i);
            }
        }
        for (int i = sw.getBranchCount() - 1; 0 <= i; i--) {
            if (sw.getBranchAt(i) instanceof Case) {
                BinaryOperator guard = KeYJavaASTFactory.equalsOperator(exV,
                    Objects.requireNonNull(((Case) sw.getBranchAt(i)).getExpression(),
                        "a case branch always carries an expression"));
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
        if (!(switchType.getJavaType() instanceof PrimitiveType)) {
            currentBlock = mkIfNullCheck(services, exV, currentBlock);
        }

        StatementBlock result;
        if (currentBlock != null) {
            result = KeYJavaASTFactory.block(s, KeYJavaASTFactory.assign(exV, switchExpr),
                currentBlock);
        } else {
            // empty switch of primitive type, the expression can still have side-effects
            result = KeYJavaASTFactory.block(s, KeYJavaASTFactory.assign(exV, switchExpr));
        }
        if (changeBreakResult.noNewBreak) {
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

    private If mkIfNullCheck(Services services, ProgramVariable var,
            @Nullable Statement elseBlock) {
        final New exception = KeYJavaASTFactory.newOperator(Objects.requireNonNull(
            services.getJavaInfo().getKeYJavaType("java.lang.NullPointerException"),
            "no KeYJavaType for java.lang.NullPointerException"));
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
    private ChangeBreakResult changeBreaks(Switch sw, Break b, boolean noNewBreak) {
        int n = sw.getBranchCount();
        Branch[] branches = new Branch[n];
        for (int i = 0; i < n; i++) {
            final ChangeBreakResult branch = Objects.requireNonNull(
                recChangeBreaks(sw.getBranchAt(i), b, noNewBreak));
            noNewBreak = branch.noNewBreak;
            branches[i] = (Branch) branch.result;
        }
        final Expression switchExpr = Objects.requireNonNull(sw.getExpression(),
            "a switch processed by switch-to-if always has an expression");
        return new ChangeBreakResult(KeYJavaASTFactory.switchBlock(switchExpr, branches),
            noNewBreak);
    }

    private @Nullable ChangeBreakResult recChangeBreaks(@Nullable ProgramElement p, Break b,
            boolean noNewBreak) {
        if (p == null) {
            return null;
        }
        if (p instanceof Break && ((Break) p).getLabel() == null) {
            return new ChangeBreakResult(b, false);
        }
        if (p instanceof Branch) {
            Statement[] s = new Statement[((Branch) p).getStatementCount()];
            for (int i = 0; i < ((Branch) p).getStatementCount(); i++) {
                final ChangeBreakResult r = Objects.requireNonNull(
                    recChangeBreaks(((Branch) p).getStatementAt(i), b, noNewBreak));
                noNewBreak = r.noNewBreak;
                s[i] = (Statement) r.result;
            }
            if (p instanceof Case) {
                return new ChangeBreakResult(KeYJavaASTFactory.caseBlock(Objects.requireNonNull(
                    ((Case) p).getExpression(), "a case branch always carries an expression"), s),
                    noNewBreak);
            }
            if (p instanceof Default) {
                return new ChangeBreakResult(
                    KeYJavaASTFactory.defaultBlock(s),
                    noNewBreak);
            }
            if (p instanceof Catch) {
                return new ChangeBreakResult(
                    KeYJavaASTFactory.catchClause(Objects.requireNonNull(
                        ((Catch) p).getParameterDeclaration(),
                        "a catch clause always declares a parameter"), s),
                    noNewBreak);
            }
            if (p instanceof Finally) {
                return new ChangeBreakResult(KeYJavaASTFactory.finallyBlock(s),
                    noNewBreak);
            }
            if (p instanceof Then) {
                return new ChangeBreakResult(
                    KeYJavaASTFactory.thenBlock(s),
                    noNewBreak);
            }
            if (p instanceof Else) {
                return new ChangeBreakResult(
                    KeYJavaASTFactory.elseBlock(s),
                    noNewBreak);
            }
        }
        if (p instanceof If) {
            // the recursion only returns null for a null subtree, which the original code
            // dereferenced unconditionally
            final ChangeBreakResult then = Objects.requireNonNull(
                recChangeBreaks(((If) p).getThen(), b, noNewBreak));
            noNewBreak = then.noNewBreak;
            final ChangeBreakResult _else = Objects.requireNonNull(
                recChangeBreaks(((If) p).getElse(), b, noNewBreak));
            noNewBreak = _else.noNewBreak;
            return new ChangeBreakResult(
                KeYJavaASTFactory.ifElse(((If) p).getExpression(),
                    (Then) then.result, (Else) _else.result),
                noNewBreak);

        }
        if (p instanceof StatementBlock) {
            Statement[] s = new Statement[((StatementBlock) p).getStatementCount()];
            for (int i = 0; i < ((StatementBlock) p).getStatementCount(); i++) {
                final ChangeBreakResult blockStmnt = Objects.requireNonNull(
                    recChangeBreaks(((StatementBlock) p).getStatementAt(i), b, noNewBreak));
                noNewBreak = blockStmnt.noNewBreak;
                s[i] = (Statement) blockStmnt.result;
            }
            return new ChangeBreakResult(
                KeYJavaASTFactory.block(s),
                noNewBreak);
        }
        if (p instanceof Try) {
            int n = ((Try) p).getBranchCount();
            Branch[] branches = new Branch[n];
            for (int i = 0; i < n; i++) {
                final ChangeBreakResult branch = Objects.requireNonNull(
                    recChangeBreaks(((Try) p).getBranchAt(i), b, noNewBreak));
                noNewBreak = branch.noNewBreak;
                branches[i] = (Branch) branch.result;
            }
            final ChangeBreakResult block = Objects.requireNonNull(
                recChangeBreaks(((Try) p).getBody(), b, noNewBreak));
            noNewBreak = block.noNewBreak;
            return new ChangeBreakResult(
                KeYJavaASTFactory
                        .tryBlock((StatementBlock) block.result, branches),
                noNewBreak);
        }
        return new ChangeBreakResult(p, noNewBreak);
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
                Statement statement = Objects.requireNonNull(
                    s.getBranchAt(i).getStatementAt(j),
                    "a branch statement of a parsed switch is never null");
                stats.add(statement);
                if (statement instanceof JumpStatement) {
                    // unconditional jump to outside the case (?)
                    break outer;
                }
            }
        }
        return KeYJavaASTFactory.block(stats);
    }

    record ChangeBreakResult(ProgramElement result, boolean noNewBreak) {
    }

}
