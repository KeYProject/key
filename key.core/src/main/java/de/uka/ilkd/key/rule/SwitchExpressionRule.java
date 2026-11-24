/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.rule;

import java.util.ArrayList;
import java.util.List;

import de.uka.ilkd.key.java.JavaTools;
import de.uka.ilkd.key.java.KeYJavaASTFactory;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.Label;
import de.uka.ilkd.key.java.ast.NonTerminalProgramElement;
import de.uka.ilkd.key.java.ast.PositionInfo;
import de.uka.ilkd.key.java.ast.ProgramElement;
import de.uka.ilkd.key.java.ast.SourceElement;
import de.uka.ilkd.key.java.ast.Statement;
import de.uka.ilkd.key.java.ast.StatementBlock;
import de.uka.ilkd.key.java.ast.StatementContainer;
import de.uka.ilkd.key.java.ast.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.ast.declaration.LocalVariableDeclaration;
import de.uka.ilkd.key.java.ast.expression.BinaryAssignment;
import de.uka.ilkd.key.java.ast.expression.Expression;
import de.uka.ilkd.key.java.ast.expression.SwitchExpression;
import de.uka.ilkd.key.java.ast.reference.ExecutionContext;
import de.uka.ilkd.key.java.ast.reference.TypeRef;
import de.uka.ilkd.key.java.ast.statement.Branch;
import de.uka.ilkd.key.java.ast.statement.Break;
import de.uka.ilkd.key.java.ast.statement.Case;
import de.uka.ilkd.key.java.ast.statement.Default;
import de.uka.ilkd.key.java.ast.statement.Else;
import de.uka.ilkd.key.java.ast.statement.If;
import de.uka.ilkd.key.java.ast.statement.LoopStatement;
import de.uka.ilkd.key.java.ast.statement.MethodFrame;
import de.uka.ilkd.key.java.ast.statement.PatternCase;
import de.uka.ilkd.key.java.ast.statement.Return;
import de.uka.ilkd.key.java.ast.statement.Then;
import de.uka.ilkd.key.java.ast.statement.Throw;
import de.uka.ilkd.key.java.ast.statement.Yield;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.Transformer;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.proof.Goal;

import org.key_project.logic.LogicServices;
import org.key_project.logic.Name;
import org.key_project.logic.op.Modality;
import org.key_project.prover.rules.RuleAbortException;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.util.collection.ImmutableList;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;

/**
 * Rewrites a statement containing a switch expression into ordinary statements, so that the
 * existing calculus can execute it.
 *
 * <p>
 * The rule evaluates the selector once into a temporary (unless it already is a variable),
 * introduces a result temporary, and emits an {@code if}-cascade whose arms assign the result
 * temporary. A {@link Yield} becomes an assignment followed by a labelled {@code break} out of its
 * arm, so that statements after a yield in the same arm are skipped.
 *
 * <p>
 * Only positions in which the switch expression is the first-evaluated operand of the statement are
 * supported; any other position aborts with a clear message (sound, incomplete). Nested switch
 * expressions are supported as the direct operand of a {@code yield}.
 */
public final class SwitchExpressionRule implements BuiltInRule {

    /** The singleton instance. */
    public static final SwitchExpressionRule INSTANCE = new SwitchExpressionRule();

    private static final Name NAME = new Name("Switch Expression");

    private SwitchExpressionRule() {
        // singleton
    }

    @Override
    public boolean isApplicable(Goal goal, PosInOccurrence occurrence) {
        if (AbstractAuxiliaryContractRule.occursNotAtTopLevelInSuccedent(occurrence)) {
            return false;
        }
        if (Transformer.inTransformer(occurrence)) {
            return false;
        }
        JTerm target = (JTerm) occurrence.subTerm();
        if (target.op() instanceof UpdateApplication) {
            target = UpdateApplication.getTarget(target);
        }
        try {
            final JavaBlock javaBlock = target.javaBlock();
            if (javaBlock == null || javaBlock.program() == null) {
                return false;
            }
            SourceElement active = JavaTools.getActiveStatement(javaBlock);
            return active instanceof Statement stmt && findSwitchExpression(stmt) != null;
        } catch (RuntimeException e) {
            return false;
        }
    }

    @Override
    public boolean isApplicableOnSubTerms() {
        return false;
    }

    @Override
    public IBuiltInRuleApp createApp(PosInOccurrence occurrence, LogicServices services) {
        return new DefaultBuiltInRuleApp<>(this, occurrence);
    }

    @Override
    public @NonNull ImmutableList<Goal> apply(Goal goal, RuleApp ruleApp)
            throws RuleAbortException {
        final Services services = goal.getOverlayServices();
        final TermBuilder tb = services.getTermBuilder();
        final PosInOccurrence occurrence = ruleApp.posInOccurrence();
        final JTerm formula = (JTerm) occurrence.subTerm();

        JTerm update = null;
        JTerm target = formula;
        if (formula.op() instanceof UpdateApplication) {
            update = UpdateApplication.getUpdate(formula);
            target = UpdateApplication.getTarget(formula);
        }

        final JavaBlock javaBlock = target.javaBlock();
        final SourceElement active = JavaTools.getActiveStatement(javaBlock);
        if (!(active instanceof Statement statement)) {
            throw new RuleAbortException("The active program element is not a statement.");
        }

        final MethodFrame frame = JavaTools.getInnermostMethodFrame(javaBlock, services);
        final ExecutionContext ec =
            frame == null ? null : (ExecutionContext) frame.getExecutionContext();

        final SwitchExpression switchExpression = hoistableSwitchExpression(statement);
        if (switchExpression == null) {
            throw new RuleAbortException(
                "Unsupported position for a switch expression: it must be the first-evaluated "
                    + "operand of its statement (initializer, assignment, return, throw, or a "
                    + "condition).");
        }

        // The contract's terms use the variable registered in the proof's namespaces; the program
        // AST may hold an equivalent but distinct instance. Use the registered instance only to
        // match the antecedent (for the selector fold); the generated program keeps the AST
        // variable.
        JTerm knownValue = null;
        boolean selectorNonNull = false;
        if (switchExpression.getSelector() instanceof ProgramVariable astVariable) {
            IProgramVariable lookedUp =
                services.getNamespaces().programVariables().lookup(astVariable.name());
            ProgramVariable registered =
                lookedUp instanceof ProgramVariable pv ? pv : astVariable;
            JTerm selectorTerm =
                services.getTypeConverter().convertToLogicElement(registered);
            if (selectorTerm != null) {
                knownValue = knownSelectorValue(goal, selectorTerm);
                selectorNonNull = knownNonNull(goal, selectorTerm);
            }
        }
        final Lowered lowered = lower(switchExpression, services, ec, knownValue,
            selectorNonNull);

        // Replace the switch expression inside the active statement by its temporary.
        JavaBlock rewritten = JavaTools.replaceStatement(javaBlock, services, switchExpression,
            lowered.variable);
        Statement newActive = (Statement) JavaTools.getActiveStatement(rewritten);

        // Prepend the temporary declarations and the if-cascade. Splice them into the enclosing
        // block when possible: a source program keeps the following statements at the same level,
        // and the prover handles the resulting if-split assumptions better that way.
        List<Statement> prelude = new ArrayList<>(lowered.prelude);
        StatementBlock parent = findEnclosingBlock(rewritten.program(), newActive);
        if (parent != null) {
            List<Statement> statements = new ArrayList<>();
            for (int i = 0; i < parent.getStatementCount(); i++) {
                Statement child = parent.getStatementAt(i);
                if (child == newActive) {
                    statements.addAll(prelude);
                }
                statements.add(child);
            }
            StatementBlock newParent = KeYJavaASTFactory.block(statements);
            rewritten = JavaTools.replaceStatement(rewritten, services, parent, newParent);
        } else {
            prelude.add(newActive);
            rewritten = JavaTools.replaceStatement(rewritten, services, newActive,
                KeYJavaASTFactory.block(prelude));
        }

        JTerm term = tb.prog(((Modality) target.op()).kind(), rewritten, target.sub(0),
            target.getLabels());
        if (update != null) {
            term = tb.apply(update, term);
        }
        // Keep the labels of the original formula (e.g. the implicit 'assignable' clause).
        term = tb.addLabel(term, formula.getLabels());

        ImmutableList<Goal> result = goal.split(1);
        result.head().changeFormula(new SequentFormula(term), occurrence);
        return result;
    }

    /**
     * Returns the switch expression of the statement if it is in a supported (first-evaluated)
     * position.
     */
    private static @Nullable SwitchExpression hoistableSwitchExpression(Statement statement) {
        if (statement instanceof Return ret
                && ret.getExpression() instanceof SwitchExpression sw) {
            return sw;
        }
        if (statement instanceof Throw thr
                && thr.getExpression() instanceof SwitchExpression sw) {
            return sw;
        }
        if (statement instanceof LocalVariableDeclaration decl) {
            var specs = decl.getVariableSpecifications();
            if (specs.size() == 1 && specs.get(0).getInitializer() instanceof SwitchExpression sw) {
                return sw;
            }
        }
        if (statement instanceof BinaryAssignment assignment
                && assignment.getChildAt(1) instanceof SwitchExpression sw
                && assignment.getChildAt(0) instanceof ProgramVariable) {
            return sw;
        }
        if (statement instanceof If ifStatement
                && ifStatement.getExpression() instanceof SwitchExpression sw) {
            return sw;
        }
        if (statement instanceof LoopStatement loop
                && loop.getGuardExpression() instanceof SwitchExpression sw) {
            return sw;
        }
        return null;
    }

    private static final class Lowered {
        final ProgramVariable variable;
        final List<Statement> prelude;

        Lowered(ProgramVariable variable, List<Statement> prelude) {
            this.variable = variable;
            this.prelude = prelude;
        }
    }

    private Lowered lower(SwitchExpression switchExpression, Services services,
            @Nullable ExecutionContext ec, @Nullable JTerm knownValue, boolean selectorNonNull)
            throws RuleAbortException {
        final var namer = services.getVariableNamer();
        final List<Statement> prelude = new ArrayList<>();

        Expression selector = switchExpression.getSelector();
        final ProgramVariable selectorVariable;
        if (selector instanceof ProgramVariable variable) {
            selectorVariable = variable;
        } else {
            TypeRef selectorType = new TypeRef(selector.getKeYJavaType(services, ec));
            selectorVariable =
                KeYJavaASTFactory.localVariable(namer.getTemporaryNameProposal("_sel"),
                    selectorType);
            prelude.add(KeYJavaASTFactory.declare(selectorVariable, selectorType));
            prelude.add(KeYJavaASTFactory.assign(selectorVariable, selector));
        }

        final TypeRef typeRef = new TypeRef(switchExpression.getKeYJavaType(services, ec));
        final ProgramVariable result =
            KeYJavaASTFactory.localVariable(namer.getTemporaryNameProposal("_sw"), typeRef);
        prelude.add(KeYJavaASTFactory.declare(result, typeRef));

        final Statement cascade =
            buildCascade(switchExpression, selectorVariable, result, services, ec, knownValue);
        if (cascade != null) {
            prelude.add(cascade);
        }

        // Java throws a NullPointerException for a null reference selector unless a case (or a
        // 'case null, default') handles null.
        if (!selectorNonNull
                && !(selector.getKeYJavaType(services, ec).getJavaType() instanceof PrimitiveType)
                && !hasNullArm(switchExpression)) {
            prelude.add(nullCheck(selectorVariable, services));
        }

        return new Lowered(result, prelude);
    }

    private Statement buildCascade(SwitchExpression switchExpression,
            ProgramVariable selectorVariable, ProgramVariable result, Services services,
            @Nullable ExecutionContext ec, @Nullable JTerm knownValue) throws RuleAbortException {
        final int count = switchExpression.getBranchCount();

        if (knownValue != null) {
            // The antecedent pins the selector to a value: pick the arm directly.
            for (int i = 0; i < count; i++) {
                if (switchExpression.getBranchAt(i) instanceof Case caseBranch) {
                    JTerm caseTerm = services.getTypeConverter()
                            .convertToLogicElement(caseBranch.getExpression(), ec);
                    if (caseTerm != null && caseTerm.equals(knownValue)) {
                        return KeYJavaASTFactory
                                .block(armBlock(switchExpression, i, result, services, ec,
                                    "_case" + i));
                    }
                }
            }
        }
        final List<Statement> statements = new ArrayList<>(count);

        int defaultIndex = -1;
        for (int i = 0; i < count; i++) {
            if (switchExpression.getBranchAt(i) instanceof Default) {
                defaultIndex = i;
                break;
            }
        }

        Statement current = null;
        if (defaultIndex >= 0) {
            current = KeYJavaASTFactory
                    .block(armBlock(switchExpression, defaultIndex, result, services, ec, "_else"));
        }
        for (int i = count - 1; i >= 0; i--) {
            final Branch branch = switchExpression.getBranchAt(i);
            if (branch instanceof Default) {
                continue;
            }
            final Expression guard;
            if (branch instanceof Case caseBranch) {
                guard = KeYJavaASTFactory.equalsOperator(selectorVariable,
                    caseBranch.getExpression());
            } else if (branch instanceof PatternCase patternCase) {
                Expression test = patternGuard(patternCase, selectorVariable);
                guard = patternCase.getGuard() == null ? test
                        : KeYJavaASTFactory.logicalAndOperator(test, patternCase.getGuard());
            } else {
                throw new RuleAbortException("Unknown switch branch: " + branch);
            }
            Statement block = KeYJavaASTFactory
                    .block(armBlock(switchExpression, i, result, services, ec, "_case" + i));
            current = current == null ? KeYJavaASTFactory.ifThen(guard, block)
                    : KeYJavaASTFactory.ifElse(guard, block, current);
        }
        return current;
    }


    private static Expression patternGuard(PatternCase patternCase, ProgramVariable selector)
            throws RuleAbortException {
        if (patternCase.getPatterns().size() != 1) {
            throw new RuleAbortException(
                "Switch labels with more than one pattern are not supported yet.");
        }
        return KeYJavaASTFactory.patternTest(selector, patternCase.getPatterns().get(0));
    }

    /**
     * Collects the statements of the arm at {@code from} (including later arms, for the
     * fall-through of colon groups), rewrites yields, and wraps the result in a labelled block so
     * that a yield can skip the rest of the arm.
     */
    private Statement armBlock(SwitchExpression switchExpression, int from, ProgramVariable result,
            Services services, @Nullable ExecutionContext ec, String labelSuggestion)
            throws RuleAbortException {
        final Label label = services.getVariableNamer().getTemporaryNameProposal(labelSuggestion);
        final List<Statement> statements = new ArrayList<>();
        for (int i = from; i < switchExpression.getBranchCount(); i++) {
            statements.addAll(lowerBody(statementsOf(switchExpression.getBranchAt(i)), result,
                label, services, ec));
            if (endsAbruptly(statements)) {
                break;
            }
        }
        return KeYJavaASTFactory.labeledStatement(label, KeYJavaASTFactory.block(statements),
            PositionInfo.UNDEFINED);
    }

    private static boolean endsAbruptly(List<Statement> statements) {
        if (statements.isEmpty()) {
            return false;
        }
        Statement last = statements.get(statements.size() - 1);
        return last instanceof Break || last instanceof Return || last instanceof Throw;
    }

    private List<Statement> lowerBody(StatementContainer container, ProgramVariable variable,
            Label label, Services services, @Nullable ExecutionContext ec)
            throws RuleAbortException {
        final List<Statement> result = new ArrayList<>();
        for (int i = 0; i < container.getStatementCount(); i++) {
            result.addAll(
                lowerStatement(container.getStatementAt(i), variable, label, services, ec));
        }
        return result;
    }

    private static List<Statement> statementsOf(Branch branch) {
        final List<Statement> statements = new ArrayList<>(branch.getStatementCount());
        for (int i = 0; i < branch.getStatementCount(); i++) {
            statements.add(branch.getStatementAt(i));
        }
        return statements;
    }

    private List<Statement> lowerStatement(Statement statement, ProgramVariable variable,
            Label label, Services services, @Nullable ExecutionContext ec)
            throws RuleAbortException {
        if (statement instanceof Yield yield) {
            return yieldReplacement(yield, variable, label, services, ec);
        }
        if (statement instanceof StatementBlock block) {
            return List.of(KeYJavaASTFactory
                    .block(lowerBody(block, variable, label, services, ec)));
        }
        if (statement instanceof If ifStatement) {
            Then thenBlock = KeYJavaASTFactory.thenBlock(
                lowerBody(ifStatement.getThen(), variable, label, services, ec)
                        .toArray(new Statement[0]));
            if (ifStatement.getElse() == null) {
                return List.of(KeYJavaASTFactory.ifThen(ifStatement.getExpression(), thenBlock));
            }
            Else elseBlock = KeYJavaASTFactory.elseBlock(
                lowerBody(ifStatement.getElse(), variable, label, services, ec)
                        .toArray(new Statement[0]));
            return List
                    .of(KeYJavaASTFactory.ifElse(ifStatement.getExpression(), thenBlock,
                        elseBlock));
        }
        if (findYield(statement) != null) {
            throw new RuleAbortException(
                "A yield inside this statement shape is not supported yet.");
        }
        return List.of(statement);
    }

    private List<Statement> yieldReplacement(Yield yield, ProgramVariable variable, Label label,
            Services services, @Nullable ExecutionContext ec) throws RuleAbortException {
        final List<Statement> statements = new ArrayList<>();
        Expression value = yield.getExpression();
        if (value instanceof SwitchExpression inner) {
            Lowered lowered = lower(inner, services, ec, null, false);
            statements.addAll(lowered.prelude);
            value = lowered.variable;
        } else if (value != null && findSwitchExpression(value) != null) {
            throw new RuleAbortException(
                "A nested switch expression is only supported as the direct operand of a yield.");
        }
        if (value == null) {
            throw new RuleAbortException("A yield statement must have an expression.");
        }
        statements.add(KeYJavaASTFactory.assign(variable, value));
        statements.add(KeYJavaASTFactory.breakStatement(label));
        return statements;
    }

    private List<Statement> lowerBody(List<Statement> statements, ProgramVariable variable,
            Label label, Services services, @Nullable ExecutionContext ec)
            throws RuleAbortException {
        final List<Statement> result = new ArrayList<>();
        for (Statement statement : statements) {
            result.addAll(lowerStatement(statement, variable, label, services, ec));
        }
        return result;
    }

    private static boolean hasNullArm(SwitchExpression switchExpression) {
        for (int i = 0; i < switchExpression.getBranchCount(); i++) {
            Branch branch = switchExpression.getBranchAt(i);
            if (branch instanceof Case caseBranch
                    && caseBranch
                            .getExpression() instanceof de.uka.ilkd.key.java.ast.expression.literal.NullLiteral) {
                return true;
            }
        }
        return false;
    }

    private static If nullCheck(ProgramVariable selectorVariable, Services services) {
        var exception = KeYJavaASTFactory.newOperator(
            services.getJavaInfo().getKeYJavaType("java.lang.NullPointerException"));
        return KeYJavaASTFactory.ifThen(KeYJavaASTFactory.equalsNullOperator(selectorVariable),
            KeYJavaASTFactory.throwClause(exception));
    }

    private static boolean knownNonNull(Goal goal, JTerm selectorTerm) {
        for (SequentFormula sequentFormula : goal.sequent().antecedent()) {
            if (!(sequentFormula.formula() instanceof JTerm formula)
                    || !(formula.op() instanceof Equality)) {
                continue;
            }
            JTerm left = formula.sub(0);
            if (left.op().name().toString().startsWith("instance<") && left.arity() == 1
                    && left.sub(0).equals(selectorTerm)
                    && formula.sub(1).op().name().toString().equals("TRUE")) {
                return true;
            }
        }
        return false;
    }

    private static @Nullable JTerm knownSelectorValue(Goal goal, JTerm selectorTerm) {
        for (SequentFormula sequentFormula : goal.sequent().antecedent()) {
            if (sequentFormula.formula() instanceof JTerm formula
                    && formula.op() instanceof Equality) {
                if (formula.sub(0).equals(selectorTerm)) {
                    return formula.sub(1);
                }
                if (formula.sub(1).equals(selectorTerm)) {
                    return formula.sub(0);
                }
            }
        }
        return null;
    }

    private static @Nullable StatementBlock findEnclosingBlock(ProgramElement element,
            Statement statement) {
        if (element instanceof StatementBlock block) {
            for (int i = 0; i < block.getStatementCount(); i++) {
                if (block.getStatementAt(i) == statement) {
                    return block;
                }
            }
        }
        if (element instanceof NonTerminalProgramElement node) {
            for (int i = 0; i < node.getChildCount(); i++) {
                StatementBlock found = findEnclosingBlock(node.getChildAt(i), statement);
                if (found != null) {
                    return found;
                }
            }
        }
        return null;
    }

    private static @Nullable Yield findYield(ProgramElement element) {
        if (element instanceof Yield yield) {
            return yield;
        }
        if (element instanceof NonTerminalProgramElement node) {
            for (int i = 0; i < node.getChildCount(); i++) {
                Yield found = findYield(node.getChildAt(i));
                if (found != null) {
                    return found;
                }
            }
        }
        return null;
    }

    private static @Nullable SwitchExpression findSwitchExpression(ProgramElement element) {
        if (element instanceof SwitchExpression sw) {
            return sw;
        }
        if (element instanceof NonTerminalProgramElement node) {
            for (int i = 0; i < node.getChildCount(); i++) {
                SwitchExpression found = findSwitchExpression(node.getChildAt(i));
                if (found != null) {
                    return found;
                }
            }
        }
        return null;
    }

    @Override
    public Name name() {
        return NAME;
    }

    @Override
    public String displayName() {
        return NAME.toString();
    }

    @Override
    public String toString() {
        return NAME.toString();
    }
}
