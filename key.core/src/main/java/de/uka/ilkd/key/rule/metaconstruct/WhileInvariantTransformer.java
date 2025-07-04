/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.metaconstruct;

import java.util.ArrayList;
import java.util.LinkedList;
import java.util.ListIterator;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.expression.literal.BooleanLiteral;
import de.uka.ilkd.key.java.statement.If;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.java.statement.TransactionStatement;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.label.TermLabelManager;
import de.uka.ilkd.key.logic.label.TermLabelState;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.ProgramSVSort;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.init.AbstractOperationPO;
import de.uka.ilkd.key.rule.Rule;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

import org.key_project.logic.op.Modality;
import org.key_project.logic.op.Operator;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.sequent.Sequent;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

public final class WhileInvariantTransformer {
    /** the outer label that is used to leave the while loop ('l1') */
    private final SchemaVariable outerLabel = SchemaVariableFactory
            .createProgramSV(new ProgramElementName("outer_label"), ProgramSVSort.LABEL, false);
    /** the inner label ('l2') */
    private final SchemaVariable innerLabel = SchemaVariableFactory
            .createProgramSV(new ProgramElementName("inner_label"), ProgramSVSort.LABEL, false);
    /** list of the labels */
    private ImmutableList<SchemaVariable> instantiations = null;

    /**
     * list of breaks that lead to abrupt termination of the loop to be transformed. Is initialised
     * by the method neededInstantiations that is invoked before calculate
     */
    private LinkedList<BreakToBeReplaced> breakList;

    /**
     * The JavaInfo object which is handed over as a parameter of calculate.
     */
    private JavaInfo javaInfo;
    private TypeConverter typeConv;
    private TermFactory tf;

    private ProgramElement body;
    private JTerm inv, post;
    private JavaNonTerminalProgramElement root;
    private Modality modality;

    private KeYJavaType returnType;

    public WhileInvariantTransformer() {
    }

    /**
     * initialises this meta operator
     *
     * @param initialPost the instantiated Term passed to the TermTransformer
     * @param invariantFramingTermination TODO
     * @param services the Services providing access to signature and type model
     */
    private void init(JTerm initialPost, JTerm invariantFramingTermination, Services services) {
        root = (JavaNonTerminalProgramElement) initialPost.javaBlock().program();
        modality = (Modality) initialPost.op();

        ReplaceWhileLoop removeWhile = new ReplaceWhileLoop(root, null, services);
        removeWhile.start();

        body = removeWhile.getTheLoop();

        // some initialisations...

        inv = invariantFramingTermination;
        post = initialPost.sub(0);

        javaInfo = services.getJavaInfo();
        tf = services.getTermFactory();
        typeConv = services.getTypeConverter();

        returnType = removeWhile.returnType();
    }

    /** calculates the resulting term. */
    public JTerm transform(TermLabelState termLabelState, Rule rule,
            RuleApp ruleApp, Goal goal,
            Sequent applicationSequent,
            PosInOccurrence applicationPos, JTerm initialPost,
            JTerm invariantFramingTermination, SVInstantiations svInst, Services services) {

        // global initialisation
        init(initialPost, invariantFramingTermination, services);

        // local initialisation
        ArrayList<ProgramElement> stmnt = new ArrayList<>();
        ArrayList<If> breakIfCascade = new ArrayList<>();

        ProgramVariable contFlag = getNewLocalvariable("cont", "boolean", services);
        ProgramVariable returnFlag = getNewLocalvariable("rtrn", "boolean", services);
        ProgramVariable breakFlag = getNewLocalvariable("brk", "boolean", services);
        // xxx how to ensure that "exc" has not been used before??
        ProgramVariable excFlag = getNewLocalvariable("exc", "boolean", services);
        ProgramVariable excParam = getNewLocalvariable("e", "java.lang.Throwable", services);
        ProgramVariable thrownException =
            getNewLocalvariable("thrownExc", "java.lang.Throwable", services);

        ProgramVariable returnExpression = null;
        if (returnType != null) {
            returnExpression = getNewLocalvariable("returnExpr", returnType, services);
        }

        JTerm contFlagTerm = null;
        JTerm returnFlagTerm = null;
        JTerm breakFlagTerm = null;
        JTerm excFlagTerm = null;

        // end of initialisation............

        int breakCounter = 0;
        final ListIterator<BreakToBeReplaced> it = breakList.listIterator(0);
        int numberOfBreaks = 0;
        while (it.hasNext()) {
            BreakToBeReplaced b = it.next();
            ProgramVariable newVar =
                getNewLocalvariable("break_" + breakCounter++, "boolean", services);
            b.setProgramVariable(newVar);
            stmnt.add(KeYJavaASTFactory.declare(newVar, BooleanLiteral.FALSE,
                javaInfo.getKeYJavaType("boolean")));
            numberOfBreaks++;
            Statement s;
            if (b.getBreak().getLabel() != null) {
                s = KeYJavaASTFactory.breakStatement(b.getBreak().getLabel());
            } else {
                s = KeYJavaASTFactory.emptyStatement();
            }
            breakIfCascade.add(KeYJavaASTFactory.ifThen(newVar, s));
        }

        WhileInvariantTransformation w = new WhileInvariantTransformation(body,
            (ProgramElementName) svInst.getInstantiation(outerLabel),
            (ProgramElementName) svInst.getInstantiation(innerLabel), contFlag, excFlag, excParam,
            thrownException, breakFlag, returnFlag, returnExpression, breakList, services);
        w.start();

        ArrayList<JTerm> resultSubterms = new ArrayList<>();

        // normal case and continue
        if (w.continueOccurred()) {
            stmnt.add(contFlagDecl(contFlag));
            contFlagTerm = services.getTermBuilder().equals(
                typeConv.convertToLogicElement(contFlag), typeConv.getBooleanLDT().getTrueTerm());
        }

        // exception case
        resultSubterms.add(throwCase(termLabelState, excFlag, thrownException, post, rule, ruleApp,
            goal, applicationPos, services));

        // return case
        if (w.returnOccurred()) {
            stmnt.add(returnFlagDecl(returnFlag, svInst));
            returnFlagTerm = typeConv.convertToLogicElement(returnFlag);
            resultSubterms.add(returnCase(termLabelState, returnFlag, returnType, returnExpression,
                post, rule, ruleApp, goal, applicationPos, services));

            if (returnType != null) {
                stmnt.add(KeYJavaASTFactory.declare(returnExpression, returnType));
            }
        }

        // break case
        if (numberOfBreaks > 0) {
            stmnt.add(breakFlagDecl(breakFlag));
            breakFlagTerm = typeConv.convertToLogicElement(breakFlag);
            resultSubterms.add(breakCase(termLabelState, breakFlag, post, breakIfCascade, rule,
                ruleApp, goal, applicationPos, services));
        }

        // we catch all exceptions
        stmnt.add(KeYJavaASTFactory.declare(excFlag, BooleanLiteral.FALSE,
            javaInfo.getKeYJavaType("boolean")));
        excFlagTerm = typeConv.convertToLogicElement(excFlag);
        stmnt.add(KeYJavaASTFactory.declare(thrownException,
            javaInfo.getKeYJavaType("java.lang.Throwable")));

        resultSubterms.add(normalCaseAndContinue(termLabelState, services, applicationPos, rule,
            ruleApp, goal, applicationSequent, contFlagTerm, returnFlagTerm, breakFlagTerm,
            excFlagTerm, AbstractOperationPO.addUninterpretedPredicateIfRequired(services, inv)));

        JTerm result = createLongJunctorTerm(Junctor.AND, resultSubterms);

        stmnt.add(w.result());
        StatementBlock s = new StatementBlock(stmnt.toArray(new Statement[0]));
        Statement resSta;
        if (svInst.getExecutionContext() != null) {
            resSta = new MethodFrame(null, svInst.getExecutionContext(), s);
        } else {
            resSta = s;
        }

        JModality.JavaModalityKind loopBodyModalityKind = modality.kind();
        final boolean transaction =
            (loopBodyModalityKind == JModality.JavaModalityKind.DIA_TRANSACTION
                    || loopBodyModalityKind == JModality.JavaModalityKind.BOX_TRANSACTION);
        JavaBlock mainJavaBlock = JavaBlock.createJavaBlock(transaction
                ? new StatementBlock(resSta,
                    new TransactionStatement(
                        de.uka.ilkd.key.java.recoderext.TransactionStatement.FINISH))
                : new StatementBlock(resSta));
        return services.getTermBuilder().prog(loopBodyModalityKind, mainJavaBlock, result,
            computeLoopBodyModalityLabels(termLabelState, services, applicationPos, rule, ruleApp,
                goal, JModality.getModality(loopBodyModalityKind, mainJavaBlock), result,
                mainJavaBlock, applicationSequent,
                initialPost.getLabels()));
    }

    /**
     * Computes the {@link TermLabel} which should be added to the created loop body modality
     * {@link JTerm}.
     *
     * @param termLabelState The {@link TermLabelState} of the current rule application.
     * @param services The {@link Services}.
     * @param applicationPos The {@link PosInOccurrence} in the {@link Sequent} to rewrite.
     * @param rule The {@link Rule} to apply.
     * @param goal The {@link Goal} to compute the result for.
     * @param loopBodyModality The {@link JModality} of the loop body.
     * @param result The postcondition of the modality.
     * @param mainJavaBlock The {@link JavaBlock} to execute within the modality.
     * @param applicationSequent The {@link Sequent} to rewrite.
     * @return The {@link TermLabel}s to add to the loop body modality {@link JTerm}.
     */
    private ImmutableArray<TermLabel> computeLoopBodyModalityLabels(TermLabelState termLabelState,
            Services services, PosInOccurrence applicationPos,
            Rule rule, RuleApp ruleApp,
            Goal goal, Operator loopBodyModality, JTerm result, JavaBlock mainJavaBlock,
            Sequent applicationSequent, ImmutableArray<TermLabel> newTermOriginalLabels) {
        return TermLabelManager.instantiateLabels(termLabelState, services, applicationPos, rule,
            ruleApp, goal, "LoopBodyModality", null,
            tf.createTerm(loopBodyModality,
                new ImmutableArray<>(result), null, newTermOriginalLabels));
    }

    /**
     * creates a new program variable
     *
     * @param varNameBase a String specifying the basename of the new variable
     * @param varType a String specifying the typename of the new variable
     * @param services the Services allowing access to the variablenaming facilities
     * @return a new program variable of the given type and a name as near as possible to the given
     *         basename
     */
    private ProgramVariable getNewLocalvariable(String varNameBase, String varType,
            Services services) {

        return getNewLocalvariable(varNameBase, javaInfo.getKeYJavaType(varType), services);

    }

    /**
     * creates a new program variable
     *
     * @param varNameBase a String specifying the basename of the new variable
     * @param varType the KeYJavaType of the new variable
     * @param services the Services allowing access to the variablenaming facilities
     * @return a new program variable of the given type and a name as near as possible to the given
     *         basename
     */
    private ProgramVariable getNewLocalvariable(String varNameBase, KeYJavaType varType,
            Services services) {
        return KeYJavaASTFactory.localVariable(
            services.getVariableNamer().getTemporaryNameProposal(varNameBase), varType);

    }

    /**
     * returns the schemavariables that are needed to transform the given loop. The unwind-loop
     * construct may need labels if unlabeled breaks and/or continues occur in the loop. Often there
     * will be uninstantiated Schemavariables in the loop that is why the found instantiations have
     * to be given.
     */
    public ImmutableList<SchemaVariable> neededInstantiations(ProgramElement originalLoop,
            SVInstantiations svInst) {
        WhileInvariantTransformation w = new WhileInvariantTransformation(originalLoop, svInst,
            javaInfo == null ? null : javaInfo.getServices());
        w.start();
        instantiations = ImmutableSLList.nil();
        if (w.innerLabelNeeded()) {
            instantiations = instantiations.prepend(innerLabel);
        }
        if (w.outerLabelNeeded()) {
            instantiations = instantiations.prepend(outerLabel);
        }
        breakList = w.breakList();
        return instantiations;
    }

    // ---------------------------------------------------------------
    // --- private helper methods to construct the result term
    // ---------------------------------------------------------------

    private JTerm createLongJunctorTerm(Junctor junctor, ArrayList<JTerm> terms) {
        if (terms.size() == 1) {
            return terms.get(0);
        } else if (terms.size() == 2) {
            return tf.createTerm(junctor, terms.get(0), terms.get(1));
        } else {
            JTerm arg1 = terms.get(0);
            terms.remove(0);
            return tf.createTerm(junctor, arg1, createLongJunctorTerm(junctor, terms));
        }
    }

    private Statement returnFlagDecl(ProgramVariable returnFlag, SVInstantiations svInst) {
        return KeYJavaASTFactory.declare(returnFlag, BooleanLiteral.FALSE,
            javaInfo.getKeYJavaType("boolean"));
    }

    private JTerm returnCase(TermLabelState termLabelState, ProgramVariable returnFlag,
            KeYJavaType returnType, ProgramVariable returnExpression, JTerm post, Rule rule,
            RuleApp ruleApp, Goal goal,
            PosInOccurrence applicationPos, Services services) {
        JavaBlock returnJavaBlock =
            addContext(root, new StatementBlock(KeYJavaASTFactory.returnClause(returnExpression)));
        JTerm executeReturn = services.getTermBuilder().prog(modality.kind(), returnJavaBlock, post,
            TermLabelManager.instantiateLabels(termLabelState, services, applicationPos, rule,
                ruleApp, goal, "ReturnCaseModality", null,
                tf.createTerm(JModality.getModality(modality.kind(), returnJavaBlock),
                    new ImmutableArray<>(post),
                    null, post.getLabels())));

        return services.getTermBuilder()
                .imp(services.getTermBuilder().equals(typeConv.convertToLogicElement(returnFlag),
                    typeConv.getBooleanLDT().getTrueTerm()), executeReturn);
    }

    private Statement breakFlagDecl(ProgramVariable breakFlag) {
        return KeYJavaASTFactory.declare(breakFlag, BooleanLiteral.FALSE,
            javaInfo.getKeYJavaType("boolean"));
    }

    private Statement contFlagDecl(ProgramVariable contFlag) {
        return KeYJavaASTFactory.declare(contFlag, BooleanLiteral.FALSE,
            javaInfo.getKeYJavaType("boolean"));
    }

    private JTerm breakCase(TermLabelState termLabelState, ProgramVariable breakFlag, JTerm post,
            ArrayList<If> breakIfCascade, Rule rule, RuleApp ruleApp,
            Goal goal,
            PosInOccurrence applicationPos, Services services) {
        JavaBlock executeJavaBlock = addContext(root,
            new StatementBlock(breakIfCascade.toArray(new Statement[0])));
        JTerm executeBreak = services.getTermBuilder().prog(modality.kind(), executeJavaBlock, post,
            TermLabelManager.instantiateLabels(termLabelState, services, applicationPos, rule,
                ruleApp, goal, "BreakCaseModality", null,
                tf.createTerm(JModality.getModality(modality.kind(), executeJavaBlock),
                    new ImmutableArray<>(post),
                    null, post.getLabels())));
        return services.getTermBuilder()
                .imp(services.getTermBuilder().equals(typeConv.convertToLogicElement(breakFlag),
                    typeConv.getBooleanLDT().getTrueTerm()), executeBreak);
    }

    private JTerm normalCaseAndContinue(TermLabelState termLabelState, Services services,
            PosInOccurrence applicationPos, Rule rule,
            RuleApp ruleApp, Goal goal,
            Sequent applicationSequent, JTerm contFlagTerm, JTerm returnFlagTerm,
            JTerm breakFlagTerm,
            JTerm excFlagTerm, JTerm inv) {

        final TermBuilder TB = services.getTermBuilder();
        final JTerm TRUE_TERM = typeConv.getBooleanLDT().getTrueTerm();

        ArrayList<JTerm> al = new ArrayList<>();

        if (returnFlagTerm != null) {
            al.add(TB.equals(returnFlagTerm, TRUE_TERM));
        }
        if (breakFlagTerm != null) {
            al.add(TB.equals(breakFlagTerm, TRUE_TERM));
        }
        if (excFlagTerm != null) {
            al.add(TB.equals(excFlagTerm, TRUE_TERM));
        }

        if (al.size() == 0) {
            if (contFlagTerm == null) {
                ImmutableArray<TermLabel> labels =
                    computeLoopBodyImplicatonLabels(termLabelState, services, applicationPos, rule,
                        ruleApp, goal, inv.op(), inv.subs(), applicationSequent);
                return TB.label(inv, labels);
            } else {
                ImmutableArray<TermLabel> labels = computeLoopBodyImplicatonLabels(termLabelState,
                    services, applicationPos, rule, ruleApp, goal, Junctor.IMP,
                    new ImmutableArray<>(contFlagTerm, inv), applicationSequent);
                return TB.imp(contFlagTerm, inv, labels);
            }
        } else {
            JTerm premiss = TB.not(createLongJunctorTerm(Junctor.OR, al));
            if (contFlagTerm != null) {
                premiss = TB.imp(contFlagTerm, premiss);
            }

            ImmutableArray<TermLabel> labels = computeLoopBodyImplicatonLabels(termLabelState,
                services, applicationPos, rule, ruleApp, goal, Junctor.IMP,
                new ImmutableArray<>(premiss, inv), applicationSequent);
            return TB.imp(premiss, contFlagTerm == null ? inv : TB.imp(contFlagTerm, inv), labels);
        }
    }

    /**
     * Computes the {@link TermLabel} which should be added to the implication of the normal
     * termination branch of a loop body.
     *
     * @param termLabelState The {@link TermLabelState} of the current rule application.
     * @param services The {@link Services}.
     * @param applicationPos The {@link PosInOccurrence} in the {@link Sequent} to rewrite.
     * @param rule The {@link Rule} to apply.
     * @param goal The {@link Goal} to compute the result for.
     * @param operator The {@link Operator} of the new {@link JTerm}.
     * @param subs The children of the new {@link JTerm}.
     * @param applicationSequent The {@link Sequent} to rewrite.
     * @return The {@link TermLabel}s to add to the new {@link JTerm}.
     */
    private ImmutableArray<TermLabel> computeLoopBodyImplicatonLabels(TermLabelState termLabelState,
            Services services, PosInOccurrence applicationPos,
            Rule rule, RuleApp ruleApp,
            Goal goal, Operator operator, ImmutableArray<JTerm> subs, Sequent applicationSequent) {
        return TermLabelManager.instantiateLabels(termLabelState, services, applicationPos, rule,
            ruleApp, goal, "LoopBodyImplication", null,
            tf.createTerm(operator, subs, null, post.getLabels()));
    }

    private JTerm throwCase(TermLabelState termLabelState, ProgramVariable excFlag,
            ProgramVariable thrownException, JTerm post, Rule rule, RuleApp ruleApp, Goal goal,
            PosInOccurrence applicationPos, Services services) {
        final TermBuilder TB = services.getTermBuilder();
        JavaBlock throwJavaBlock =
            addContext(root, new StatementBlock(KeYJavaASTFactory.throwClause(thrownException)));
        // TODO: can we simplify this? Why create same term twice? Can `prog` be used?
        JTerm throwException = TB.prog(modality.kind(), throwJavaBlock, post,
            TermLabelManager.instantiateLabels(termLabelState, services, applicationPos, rule,
                ruleApp, goal, "ThrowCaseModality", null,
                tf.createTerm(JModality.getModality(modality.kind(), throwJavaBlock),
                    new ImmutableArray<>(post), null,
                    post.getLabels())));
        return TB.imp(TB.equals(typeConv.convertToLogicElement(excFlag),
            typeConv.getBooleanLDT().getTrueTerm()), throwException);
    }

    private JavaBlock addContext(JavaNonTerminalProgramElement root, StatementBlock block) {
        ReplaceWhileLoop replaceWhile = new ReplaceWhileLoop(root, block, javaInfo.getServices());
        replaceWhile.start();

        return JavaBlock.createJavaBlock((StatementBlock) replaceWhile.result());

    }
}
