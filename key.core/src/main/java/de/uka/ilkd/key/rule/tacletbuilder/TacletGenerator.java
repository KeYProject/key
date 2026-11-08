/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.rule.tacletbuilder;

import java.util.*;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.ContextStatementBlock;
import de.uka.ilkd.key.java.ast.Statement;
import de.uka.ilkd.key.java.ast.StatementBlock;
import de.uka.ilkd.key.java.ast.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.ast.declaration.ClassDeclaration;
import de.uka.ilkd.key.java.ast.statement.MethodBodyStatement;
import de.uka.ilkd.key.ldt.JavaDLTheory;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.ProgramSVSort;
import de.uka.ilkd.key.proof.OpReplacer;
import de.uka.ilkd.key.proof.calculus.JavaDLSequentKit;
import de.uka.ilkd.key.rule.RewriteTaclet;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.speclang.HeapContext;

import org.key_project.logic.ChoiceExpr;
import org.key_project.logic.Name;
import org.key_project.logic.op.Operator;
import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.logic.sort.Sort;
import org.key_project.prover.rules.ApplicationRestriction;
import org.key_project.prover.rules.RuleSet;
import org.key_project.prover.sequent.Sequent;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSet;
import org.key_project.util.collection.Pair;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;



/**
 *
 * @author christoph
 */
@NullMarked
public class TacletGenerator {

    private static final TacletGenerator instance = new TacletGenerator();


    private TacletGenerator() {
    }


    public static TacletGenerator getInstance() {
        return instance;
    }


    private TacletGoalTemplate createAxiomGoalTemplate(JTerm goalTerm) {
        final SequentFormula axiomSf = new SequentFormula(goalTerm);
        final ImmutableList<SequentFormula> axiomSemiSeq =
            ImmutableList.singleton(axiomSf);
        final Sequent axiomSeq = JavaDLSequentKit.createAnteSequent(axiomSemiSeq);
        final TacletGoalTemplate axiomTemplate =
            new TacletGoalTemplate(axiomSeq, ImmutableList.nil());
        return axiomTemplate;
    }


    /**
     * Returns a no-find taclet to the passed axiom. If the axiom expression does not contain
     * reference to self, it is considered as if it were static.
     */
    public Taclet generateAxiomTaclet(Name tacletName, JTerm originalAxiom,
            ImmutableList<LocationVariable> programVars, KeYJavaType kjt, RuleSet ruleSet,
            TermServices services) {
        // create schema terms
        final ImmutableList<JOperatorSV> schemaVars = createSchemaVariables(programVars);
        final TermAndBoundVarPair schemaAxiom = createSchemaTerm(originalAxiom,
            widenProgramVars(programVars), widenSchemaVars(schemaVars), services);

        // create taclet
        NoFindTacletBuilder tacletBuilder = new NoFindTacletBuilder();
        tacletBuilder.setName(tacletName);
        tacletBuilder.addTacletGoalTemplate(createAxiomGoalTemplate(schemaAxiom.term));
        tacletBuilder.addVarsNotFreeIn(schemaAxiom.boundVars, schemaVars);
        tacletBuilder.addRuleSet(ruleSet);
        return tacletBuilder.getTaclet();
    }


    public Taclet generateRewriteTaclet(Name tacletName, JTerm originalFind, JTerm originalAxiom,
            ImmutableList<LocationVariable> programVars, RuleSet ruleSet, TermServices services) {
        // create schema terms
        final ImmutableList<JOperatorSV> schemaVars = createSchemaVariables(programVars);
        final TermAndBoundVarPair schemaFind =
            createSchemaTerm(originalFind, widenProgramVars(programVars),
                widenSchemaVars(schemaVars), services);
        final TermAndBoundVarPair schemaAxiom =
            createSchemaTerm(originalAxiom, widenProgramVars(programVars),
                widenSchemaVars(schemaVars), services);
        final ImmutableSet<VariableSV> boundSVs = schemaFind.boundVars.union(schemaAxiom.boundVars);

        // create taclet
        RewriteTacletBuilder<RewriteTaclet> tacletBuilder = new RewriteTacletBuilder<>();
        tacletBuilder.setName(tacletName);
        tacletBuilder.setFind(schemaFind.term);
        tacletBuilder.addGoalTerm(schemaAxiom.term);
        tacletBuilder.addVarsNotFreeIn(boundSVs, schemaVars);
        tacletBuilder.addRuleSet(ruleSet);
        return tacletBuilder.getTaclet();
    }


    // selfSV is null for static targets; the resulting \notfreein condition without a self
    // schema variable is meaningless but preserved as in the original code.
    @SuppressWarnings({ "NullAway", "nullness:argument.type.incompatible" })
    public Taclet generateRelationalRepresentsTaclet(Name tacletName, JTerm originalAxiom,
            KeYJavaType kjt, IObserverFunction target, List<LocationVariable> heaps,
            @Nullable LocationVariable self, ImmutableList<LocationVariable> paramVars,
            Map<LocationVariable, LocationVariable> atPreVars, boolean satisfiabilityGuard,
            TermServices services) {
        final RewriteTacletBuilder<RewriteTaclet> tacletBuilder = new RewriteTacletBuilder<>();

        TermBuilder tb = services.getTermBuilder();
        originalAxiom = tb.convertToFormula(originalAxiom);

        // create schema terms
        ImmutableList<@Nullable LocationVariable> pvs = ImmutableList.nil();
        ImmutableList<@Nullable JOperatorSV> svs = ImmutableList.nil();
        List<TermSV> heapSVs = new ArrayList<>();
        for (LocationVariable heap : heaps) {
            if (target.getStateCount() >= 1) {
                pvs = pvs.append(heap);
                var heapSV = createSchemaVariable(heap);
                svs = svs.append(heapSV);
                heapSVs.add(heapSV);
                if (target.getStateCount() == 2) {
                    pvs = pvs.append(atPreVars.get(heap));
                    heapSV = createSchemaVariable(atPreVars.get(heap));
                    svs = svs.append(heapSV);
                    heapSVs.add(heapSV);
                }
            }
        }

        final @Nullable JOperatorSV selfSV = createSchemaVariable(self);

        ImmutableList<JOperatorSV> paramSVs = ImmutableList.nil();
        for (LocationVariable paramVar : paramVars) {
            paramSVs = paramSVs.append(
                Objects.requireNonNull(createSchemaVariable(paramVar),
                    "no schema variable for " + paramVar));
        }
        pvs = pvs.append(self).append(paramVars);
        svs = svs.append(selfSV).append(paramSVs);

        final TermAndBoundVarPair schemaAxiom = createSchemaTerm(originalAxiom, pvs, svs, services);

        // create goal template
        SequentFormula guardedSchemaAxiom = generateGuard(kjt, target, services, selfSV, heapSVs,
            paramSVs, schemaAxiom.term, tacletBuilder, satisfiabilityGuard);
        final Sequent addedSeq = JavaDLSequentKit.createAnteSequent(
            ImmutableList.singleton(guardedSchemaAxiom));
        ImmutableList<JTerm> vars = ImmutableList.nil();
        for (TermSV heapSV : heapSVs) {
            vars = vars.append(tb.var(heapSV));
        }
        if (!target.isStatic()) {
            vars = vars.append(
                tb.var(Objects.requireNonNull(selfSV, "no self schema variable for " + target)));
        }
        for (JOperatorSV sv : paramSVs) {
            vars = vars.append(tb.var(sv));
        }
        final JTerm findTerm = tb.func(target, vars.toArray(new JTerm[0]));

        final RewriteTacletGoalTemplate axiomTemplate =
            new RewriteTacletGoalTemplate(addedSeq, ImmutableList.nil(), findTerm);

        // choices, rule set
        // Be careful that the choices used here is actually declared (see optionsDeclarations.key),
        // otherwise the taclet will be unusable!
        var choice = ChoiceExpr.variable("modelFields",
            satisfiabilityGuard ? "showSatisfiability" : "treatAsAxiom");
        final RuleSet ruleSet = new RuleSet(
            new Name(satisfiabilityGuard ? "inReachableStateImplication" : "classAxiom"));

        // create taclet
        tacletBuilder.setName(tacletName);
        tacletBuilder.setChoices(choice);
        tacletBuilder.setFind(findTerm);
        tacletBuilder.addTacletGoalTemplate(axiomTemplate);
        tacletBuilder.addVarsNotFreeIn(schemaAxiom.boundVars, selfSV);
        tacletBuilder.setApplicationRestriction(
            new ApplicationRestriction(ApplicationRestriction.SAME_UPDATE_LEVEL));
        for (SchemaVariable heapSV : heapSVs) {
            tacletBuilder.addVarsNotFreeIn(schemaAxiom.boundVars, heapSV);
        }
        for (SchemaVariable paramSV : paramSVs) {
            tacletBuilder.addVarsNotFreeIn(schemaAxiom.boundVars, paramSV);
        }

        tacletBuilder.addRuleSet(ruleSet);
        return tacletBuilder.getTaclet();
    }


    public ImmutableSet<Taclet> generateFunctionalRepresentsTaclets(Name name,
            @Nullable JTerm originalPreTerm,
            JTerm originalRepresentsTerm, KeYJavaType kjt, IObserverFunction target,
            List<LocationVariable> heaps, @Nullable LocationVariable self,
            ImmutableList<LocationVariable> paramVars,
            Map<LocationVariable, LocationVariable> atPreVars,
            ImmutableSet<Pair<Sort, IObserverFunction>> toLimit, boolean satisfiability,
            Services services) {
        ImmutableSet<Taclet> result = DefaultImmutableSet.nil();
        TermBuilder TB = services.getTermBuilder();

        // instantiate axiom with schema variables
        ImmutableList<@Nullable LocationVariable> pvs = ImmutableList.nil();
        ImmutableList<@Nullable JOperatorSV> svs = ImmutableList.nil();
        List<TermSV> heapSVs = new ArrayList<>();
        for (var heap : heaps) {
            if (target.getStateCount() >= 1) {
                pvs = pvs.append(heap);
                TermSV heapSV = createSchemaVariable(heap);
                svs = svs.append(heapSV);
                heapSVs.add(heapSV);
                if (target.getStateCount() == 2) {
                    pvs = pvs.append(atPreVars.get(heap));
                    heapSV = createSchemaVariable(atPreVars.get(heap));
                    svs = svs.append(heapSV);
                    heapSVs.add(heapSV);
                }
            }
        }

        final @Nullable TermSV selfSV = createSchemaVariable(self);
        ImmutableList<JOperatorSV> paramSVs = ImmutableList.nil();
        for (ProgramVariable paramVar : paramVars) {
            paramSVs = paramSVs.append(
                Objects.requireNonNull(createSchemaVariable(paramVar),
                    "no schema variable for " + paramVar));
        }
        pvs = pvs.append(self).append(widenProgramVars(paramVars));
        svs = svs.append(selfSV).append(widenSchemaVars(paramSVs));
        final TermAndBoundVarPair schemaRepresents =
            createSchemaTerm(originalRepresentsTerm, pvs, svs, services);
        assert schemaRepresents.term.op() instanceof Equality;
        final JTerm schemaLhs = schemaRepresents.term.sub(0);
        final JTerm schemaRhs = schemaRepresents.term.sub(1);

        // limit observers
        final Pair<JTerm, ImmutableSet<Taclet>> limited = limitTerm(schemaRhs, toLimit, services);
        final JTerm limitedRhs = limited.first;
        result = result.union(limited.second);

        // create if sequent
        final boolean finalClass = kjt.getJavaType() instanceof ClassDeclaration
                && ((ClassDeclaration) kjt.getJavaType()).isFinal();
        final Sequent ifSeq;
        if (target.isStatic()) {
            ifSeq = null;
        } else if (finalClass) {
            /*
             * part of fix for #1598 invariants for final class should not be applied to null
             * \assumes ( ==> self = null )
             */
            // ifSeq = null;
            final JTerm ifFormula = TB.equals(
                TB.var(Objects.requireNonNull(selfSV, "no self schema variable for " + target)),
                TB.NULL());
            final SequentFormula ifCf = new SequentFormula(ifFormula);
            ifSeq = JavaDLSequentKit.createSuccSequent(ImmutableList.singleton(ifCf));
        } else {
            /* \assumes ( Sort.exactInstance(self) ==> ) */
            final JTerm ifFormula =
                TB.exactInstance(Objects.requireNonNull(kjt.getSort(), "no sort for " + kjt),
                    TB.var(Objects.requireNonNull(selfSV,
                        "no self schema variable for " + target)));
            final SequentFormula ifCf = new SequentFormula(ifFormula);
            ifSeq = JavaDLSequentKit.createAnteSequent(ImmutableList.singleton(ifCf));
        }

        JTerm addForumlaTerm = originalPreTerm;
        // The presence of the precondition term means we are dealing with a model method definition
        // taclet, an \add section to check preconditions has to be added
        // FIXME does this also affect the satisfiability branches?
        if (addForumlaTerm != null) {
            JTerm wfFormula = null;
            JTerm createdFormula = null;
            for (var heapSV : heapSVs) {
                final JTerm wf = TB.wellFormed(TB.var(heapSV));
                if (wfFormula == null) {
                    wfFormula = wf;
                } else {
                    wfFormula = TB.and(wfFormula, wf);
                }
                if (!target.isStatic()) {
                    final JTerm crf = TB.created(TB.var(heapSV),
                        TB.var(Objects.requireNonNull(selfSV,
                            "no self schema variable for " + target)));
                    if (createdFormula == null) {
                        createdFormula = crf;
                    } else {
                        createdFormula = TB.and(createdFormula, crf);
                    }
                }
            }
            final JTerm selfNull = target.isStatic() ? null
                    : TB.equals(TB.var(Objects.requireNonNull(selfSV,
                        "no self schema variable for " + target)), TB.NULL());
            if (wfFormula != null) {
                addForumlaTerm = TB.and(addForumlaTerm, wfFormula);
            }
            if (createdFormula != null) {
                addForumlaTerm = TB.and(addForumlaTerm, createdFormula);
            }
            if (selfNull != null) {
                addForumlaTerm = TB.and(addForumlaTerm, TB.not(selfNull));
            }

        }

        // create taclet
        final RewriteTacletBuilder<RewriteTaclet> tacletBuilder = new RewriteTacletBuilder<>();
        tacletBuilder.setFind(schemaLhs);
        tacletBuilder.addTacletGoalTemplate(
            new RewriteTacletGoalTemplate(JavaDLSequentKit.getInstance().getEmptySequent(),
                ImmutableList.nil(), limitedRhs));

        // FIXME - there is a chance this will have to go along with all the other associated
        // changes
        /*
         * if(addedSeq != null) { TacletGoalTemplate tgc = new TacletGoalTemplate(addedSeq,
         * ImmutableSLList.<Taclet>nil()); tgc.setName("Precondition of "+target.name());
         * tacletBuilder.addTacletGoalTemplate (tgc); }
         */
        if (ifSeq != null) {
            tacletBuilder.setAssumesSequent(ifSeq);
        }
        tacletBuilder.setName(name);
        tacletBuilder.addRuleSet(new RuleSet(new Name("classAxiom")));
        if (satisfiability) {
            tacletBuilder.addRuleSet(new RuleSet(new Name("split")));
        }
        for (VariableSV boundSV : schemaRepresents.boundVars) {
            for (SchemaVariable heapSV : heapSVs) {
                tacletBuilder.addVarsNotFreeIn(boundSV, heapSV);
            }
            if (selfSV != null) {
                tacletBuilder.addVarsNotFreeIn(boundSV, selfSV);
            }
            for (SchemaVariable paramSV : paramSVs) {
                tacletBuilder.addVarsNotFreeIn(boundSV, paramSV);
            }
        }
        var c = ChoiceExpr.variable("modelFields",
            satisfiability ? "showSatisfiability" : "treatAsAxiom");
        tacletBuilder.setChoices(c);

        if (satisfiability) {
            functionalRepresentsAddSatisfiabilityBranch(target, services, heapSVs, selfSV, paramSVs,
                schemaRepresents, tacletBuilder);
        }
        tacletBuilder.setApplicationRestriction(
            new ApplicationRestriction(ApplicationRestriction.SAME_UPDATE_LEVEL));
        result = result.add(tacletBuilder.getTaclet());
        // return
        return result;
    }


    private void functionalRepresentsAddSatisfiabilityBranch(IObserverFunction target,
            TermServices services, List<TermSV> heapSVs, final @Nullable JOperatorSV selfSV,
            ImmutableList<JOperatorSV> paramSVs, final TermAndBoundVarPair schemaRepresents,
            final RewriteTacletBuilder<? extends RewriteTaclet> tacletBuilder) {
        final JTerm axiomSatisfiable = functionalRepresentsSatisfiability(target, services, heapSVs,
            selfSV, paramSVs, schemaRepresents, tacletBuilder);
        SequentFormula addedCf = new SequentFormula(axiomSatisfiable);
        final Sequent addedSeq =
            JavaDLSequentKit.createSuccSequent(ImmutableList.singleton(addedCf));
        final var skolemSV =
            SchemaVariableFactory.createSkolemTermSV(new Name("sk"), target.sort());
        for (SchemaVariable heapSV : heapSVs) {
            tacletBuilder.addVarsNewDependingOn(skolemSV, heapSV);
        }
        if (!target.isStatic()) {
            tacletBuilder.addVarsNewDependingOn(skolemSV, Objects.requireNonNull(selfSV,
                "no self schema variable for " + target));
        }
        for (SchemaVariable paramSV : paramSVs) {
            tacletBuilder.addVarsNewDependingOn(skolemSV, paramSV);
        }
        tacletBuilder.addTacletGoalTemplate(new RewriteTacletGoalTemplate(addedSeq,
            ImmutableList.nil(), services.getTermBuilder().var(skolemSV)));
        tacletBuilder.goalTemplates().tail().head().setName("Use Axiom");
        tacletBuilder.goalTemplates().head().setName("Show Axiom Satisfiability");
    }


    private JTerm functionalRepresentsSatisfiability(IObserverFunction target,
            TermServices services,
            List<TermSV> heapSVs, final @Nullable JOperatorSV selfSV,
            ImmutableList<JOperatorSV> paramSVs, final TermAndBoundVarPair schemaRepresents,
            final RewriteTacletBuilder<? extends RewriteTaclet> tacletBuilder) {
        ImmutableList<JTerm> vars = ImmutableList.nil();
        TermBuilder TB = services.getTermBuilder();
        for (var heapSV : heapSVs) {
            vars = vars.append(TB.var(heapSV));
        }
        if (!target.isStatic()) {
            vars = vars.append(TB.var(Objects.requireNonNull(selfSV,
                "no self schema variable for " + target)));
        }
        for (var sv : paramSVs) {
            vars = vars.append(TB.var(sv));
        }
        final JTerm targetTerm = TB.func(target, vars.toArray(new JTerm[0]));

        final JTerm axiomSatisfiable;
        if (target.sort() == JavaDLTheory.FORMULA) {
            axiomSatisfiable = TB.or(
                OpReplacer.replace(targetTerm, TB.tt(), schemaRepresents.term,
                    services.getTermFactory()),
                OpReplacer.replace(targetTerm, TB.ff(), schemaRepresents.term,
                    services.getTermFactory()));
        } else {
            final VariableSV targetSV = SchemaVariableFactory.createVariableSV(
                new Name(target.sort().name().toString().substring(0, 1)), target.sort());
            JTerm targetSVReachable = null;
            for (var heapSV : heapSVs) {
                tacletBuilder.addVarsNotFreeIn(targetSV, heapSV);
                final JTerm tReach =
                    TB.reachableValue(TB.var(heapSV), TB.var(targetSV),
                        Objects.requireNonNull(target.getType(), "no result type of " + target));
                if (targetSVReachable == null) {
                    targetSVReachable = tReach;
                } else {
                    targetSVReachable = TB.and(targetSVReachable, tReach);
                }
            }
            if (!target.isStatic()) {
                tacletBuilder.addVarsNotFreeIn(targetSV, Objects.requireNonNull(selfSV,
                    "no self schema variable for " + target));
            }
            for (SchemaVariable paramSV : paramSVs) {
                tacletBuilder.addVarsNotFreeIn(targetSV, paramSV);
            }
            final var replaced = OpReplacer.replace(targetTerm,
                TB.var(targetSV), schemaRepresents.term, services.getTermFactory());
            if (targetSVReachable == null) { // no heaps are given e.g. no_state method
                axiomSatisfiable = TB.ex(targetSV, replaced);
            } else {
                axiomSatisfiable = TB.ex(targetSV, TB.and(targetSVReachable, replaced));
            }
        }
        return axiomSatisfiable;
    }

    public ImmutableSet<Taclet> generateContractAxiomTaclets(Name name, JTerm originalPre,
            JTerm originalFreePre, JTerm originalPost, JTerm originalFreePost, JTerm originalMby,
            KeYJavaType kjt, IObserverFunction target, List<LocationVariable> heaps,
            @Nullable LocationVariable originalSelfVar, LocationVariable originalResultVar,
            Map<LocationVariable, LocationVariable> atPreVars,
            ImmutableList<LocationVariable> originalParamVars,
            ImmutableSet<Pair<Sort, IObserverFunction>> toLimit, boolean satisfiabilityGuard,
            TermServices services) {

        ImmutableList<@Nullable LocationVariable> pvs = ImmutableList.nil();
        ImmutableList<@Nullable JOperatorSV> svs = ImmutableList.nil();
        final List<TermSV> heapSVs = new ArrayList<>();
        for (var heap : heaps) {
            if (target.getStateCount() >= 1) {
                pvs = pvs.append(heap);
                var sv = SchemaVariableFactory.createTermSV(
                    new Name("sv_" + heap.name()), heap.sort(), false, false);
                svs = svs.append(sv);
                heapSVs.add(sv);
                if (target.getStateCount() == 2) {
                    LocationVariable preHeap =
                        Objects.requireNonNull(atPreVars.get(heap), "no pre-heap for " + heap);
                    pvs = pvs.append(preHeap);
                    sv = SchemaVariableFactory.createTermSV(
                        new Name("sv_" + preHeap.name()), heap.sort(), false,
                        false);
                    svs = svs.append(sv);
                    heapSVs.add(sv);
                }
            }
        }
        final var selfSV = target.isStatic() ? null
                : SchemaVariableFactory.createTermSV(new Name("sv_self"),
                    Objects.requireNonNull(kjt.getSort(), "no sort for " + kjt), false,
                    false);
        final JOperatorSV[] paramSVs = new JOperatorSV[target.getNumParams()];
        for (int i = 0; i < paramSVs.length; i++) {
            KeYJavaType paramType = Objects.requireNonNull(target.getParamType(i),
                "no parameter type " + i + " of " + target);
            paramSVs[i] = SchemaVariableFactory.createTermSV(new Name("sv_p" + i),
                Objects.requireNonNull(paramType.getSort(), "no sort for " + paramType), false,
                false);
        }
        // final SchemaVariable resultSV = SchemaVariableFactory.createTermSV(new Name("sv_r"),
        // target.getType().getSort(), false, false);

        final RewriteTacletBuilder<RewriteTaclet> tacletBuilder = new RewriteTacletBuilder<>();

        JTerm wfFormula = null;
        JTerm createdFormula = null;
        TermBuilder TB = services.getTermBuilder();
        for (var heapSV : heapSVs) {
            final JTerm wf = TB.wellFormed(TB.var(heapSV));
            if (wfFormula == null) {
                wfFormula = wf;
            } else {
                wfFormula = TB.and(wfFormula, wf);
            }
            if (!target.isStatic()) {
                final JTerm crf = TB.created(TB.var(heapSV),
                    TB.var(Objects.requireNonNull(selfSV,
                        "no self schema variable for " + target)));
                if (createdFormula == null) {
                    createdFormula = crf;
                } else {
                    createdFormula = TB.and(createdFormula, crf);
                }
            }
        }
        final JTerm selfNull = target.isStatic() ? null
                : TB.equals(TB.var(Objects.requireNonNull(selfSV,
                    "no self schema variable for " + target)), TB.NULL());
        final JTerm mbyOK = originalMby != null ? TB.measuredByCheck(originalMby) : null;

        // create find
        final JTerm[] subs = new JTerm[target.arity()];
        int i = 0;
        for (var heapSV : heapSVs) {
            subs[i++] = TB.var(heapSV);
        }
        if (!target.isStatic()) {
            subs[i++] =
                TB.var(Objects.requireNonNull(selfSV, "no self schema variable for " + target));
        }
        for (int j = 0; j < paramSVs.length; j++) {
            subs[j + i] = TB.var(paramSVs[j]);
        }
        final JTerm find = TB.func(target, subs);

        // build taclet
        JTerm addFormulaTerm = originalPre;
        if (wfFormula != null) {
            addFormulaTerm = TB.and(addFormulaTerm, wfFormula);
        }
        if (createdFormula != null) {
            addFormulaTerm = TB.and(addFormulaTerm, createdFormula);
        }
        if (selfNull != null) {
            addFormulaTerm = TB.and(addFormulaTerm, TB.not(selfNull));
        }
        if (mbyOK != null) {
            addFormulaTerm = TB.and(addFormulaTerm, mbyOK);
        }

        pvs = pvs.append(originalSelfVar).append(widenProgramVars(originalParamVars));
        // .append(originalResultVar)
        svs = svs.append(selfSV).append(paramSVs); // .append(resultSV)
        final TermAndBoundVarPair schemaAdd = createSchemaTerm(
            TB.imp(addFormulaTerm,
                OpReplacer.replace(TB.var(originalResultVar), find,
                    TB.and(originalPost, originalFreePost), services.getTermFactory())),
            pvs, svs, services);

        final JTerm addedFormula = schemaAdd.term;
        final SequentFormula addedCf = new SequentFormula(addedFormula);
        final Sequent addedSeq = JavaDLSequentKit.createAnteSequent(
            ImmutableList.singleton(addedCf));

        for (VariableSV boundSV : schemaAdd.boundVars) {
            for (SchemaVariable heapSV : heapSVs) {
                tacletBuilder.addVarsNotFreeIn(boundSV, heapSV);
            }
            if (selfSV != null) {
                tacletBuilder.addVarsNotFreeIn(boundSV, selfSV);
            }
            for (SchemaVariable paramSV : paramSVs) {
                tacletBuilder.addVarsNotFreeIn(boundSV, paramSV);
            }
            // tacletBuilder.addVarsNotFreeIn(boundSV, resultSV);
        }

        tacletBuilder.setFind(find);
        tacletBuilder.setApplicationRestriction(
            new ApplicationRestriction(ApplicationRestriction.SAME_UPDATE_LEVEL));
        tacletBuilder.addTacletGoalTemplate(
            new TacletGoalTemplate(addedSeq, ImmutableList.nil()));
        tacletBuilder.setName(name);
        tacletBuilder.addRuleSet(new RuleSet(new Name("classAxiom")));

        return DefaultImmutableSet.<Taclet>nil().add(tacletBuilder.getTaclet());

    }

    // FIXME Wojtek: This method is currently not used, hence declared private, but it should stay
    // uncommented as
    // to keep the development of model methods consistent
    // At this point I am not even certain what this method was for...
    private ImmutableSet<Taclet> generateModelMethodExecutionTaclets(Name name, KeYJavaType kjt,
            IObserverFunction target, Services services) {
        TermBuilder TB = services.getTermBuilder();

        final ProgramSV selfProgSV = target.isStatic() ? null
                : SchemaVariableFactory.createProgramSV(new ProgramElementName("#self_sv"),
                    ProgramSVSort.VARIABLE, false);

        // final ProgramSV heapProgSV = target.getStateCount() == 2 ?
        // SchemaVariableFactory.createProgramSV(new ProgramElementName("#heap_sv"),
        // ProgramSVSort.VARIABLE, false)
        // : null;

        final ProgramSV[] paramProgSVs = new ProgramSV[target.getNumParams()];
        for (int i = 0; i < paramProgSVs.length; i++) {
            paramProgSVs[i] = SchemaVariableFactory.createProgramSV(
                new ProgramElementName("#p_sv_" + i), ProgramSVSort.VARIABLE, false);
        }
        final ProgramSV resultProgSV = SchemaVariableFactory
                .createProgramSV(new ProgramElementName("#res_sv"), ProgramSVSort.VARIABLE, false);

        final ImmutableList<KeYJavaType> sig = ImmutableList.<KeYJavaType>nil()
                .append(Objects.requireNonNull(target.getParamTypes(),
                    "no parameter types of " + target));
        final IProgramMethod targetImpl = Objects.requireNonNull(services.getJavaInfo()
                .getProgramMethod(kjt, ((ProgramMethod) target).getName(), sig, kjt),
            "no program method " + target + " in " + kjt);

        // The receiver is null for static targets; MethodBodyStatement then substitutes the
        // method's container type as context (see its constructor), so null is legitimate here.
        @SuppressWarnings({ "NullAway", "nullness:argument.type.incompatible" })
        final MethodBodyStatement mbs = new MethodBodyStatement(targetImpl, selfProgSV,
            resultProgSV, new ImmutableArray<>(paramProgSVs));
        final JavaBlock findBlock =
            JavaBlock.createJavaBlock(contextStatementBlock(mbs));

        final var modalitySV =
            SchemaVariableFactory.createModalOperatorSV(new Name("#allModal_sv"),
                JavaDLTheory.FORMULA,
                DefaultImmutableSet.<JModality.JavaModalityKind>nil()
                        .add(JModality.JavaModalityKind.DIA)
                        .add(JModality.JavaModalityKind.BOX)
                        .add(JModality.JavaModalityKind.DIA_TRANSACTION)
                        .add(JModality.JavaModalityKind.BOX_TRANSACTION));
        var postSV = SchemaVariableFactory.createFormulaSV(new Name("#post_sv"));

        final JTerm findTerm = createTermWithoutLabels(TB.tf(),
            JModality.getModality(modalitySV, findBlock),
            new JTerm[] { TB.var(postSV) }, null);

        final JavaBlock replaceBlock =
            JavaBlock.createJavaBlock(contextStatementBlock(new StatementBlock()));

        final JTerm[] updateSubs = new JTerm[target.arity()];
        int i = 0;
        updateSubs[i++] =
            TB.var(Objects.requireNonNull(services.getTypeConverter().getHeapLDT(),
                "no heap LDT").getHeap());
        if (target.getStateCount() == 2) {
            updateSubs[i++] =
                TB.var(Objects.requireNonNull(services.getTypeConverter().getHeapLDT(),
                    "no heap LDT").getHeap());
        }
        if (!target.isStatic()) {
            updateSubs[i++] = TB.var(Objects.requireNonNull(selfProgSV,
                "no self program schema variable for " + target));
        }
        for (int j = 0; j < paramProgSVs.length; j++) {
            updateSubs[j + i] = TB.var(paramProgSVs[j]);
        }

        final JTerm replaceTerm =
            TB.apply(TB.elementary(TB.var(resultProgSV), TB.func(target, updateSubs)),
                createTermWithoutLabels(TB.tf(),
                    JModality.getModality(modalitySV, replaceBlock),
                    new JTerm[] { TB.var(postSV) }, null));

        final RewriteTacletBuilder<RewriteTaclet> replaceTacletBuilder =
            new RewriteTacletBuilder<>();

        replaceTacletBuilder.setFind(findTerm);
        replaceTacletBuilder.setApplicationRestriction(
            new ApplicationRestriction(ApplicationRestriction.SAME_UPDATE_LEVEL));
        replaceTacletBuilder.addTacletGoalTemplate(new RewriteTacletGoalTemplate(replaceTerm));
        replaceTacletBuilder.setName(name);
        replaceTacletBuilder.addRuleSet(new RuleSet(new Name("simplify_prog"))); // TODO ?

        return DefaultImmutableSet.<Taclet>nil().add(replaceTacletBuilder.getTaclet());

    }


    public ImmutableSet<Taclet> generatePartialInvTaclet(Name name, List<TermSV> heapSVs,
            JOperatorSV selfSV, JOperatorSV eqSV, JTerm term, KeYJavaType kjt,
            ImmutableSet<Pair<Sort, IObserverFunction>> toLimit, boolean isStatic, boolean isFree,
            boolean eqVersion, Services services) {
        TermBuilder TB = services.getTermBuilder();
        ImmutableSet<Taclet> result = DefaultImmutableSet.nil();
        Map<JTerm, JTerm> replace = new LinkedHashMap<>();
        int i = 0;
        for (ProgramVariable heap : HeapContext.getModifiableHeaps(services, false)) {
            replace.put(TB.var(heap), TB.var(heapSVs.get(i++)));
        }
        final OpReplacer replacer = new OpReplacer(replace, services.getTermFactory());
        // TB.getBaseHeap(services), TB.var(heapSV)
        // instantiate axiom with schema variables
        final JTerm rawAxiom =
            Objects.requireNonNull(replacer.replace(term), "no replacement result for " + term);
        final TermAndBoundVarPair schemaAxiom = replaceBoundLogicVars(rawAxiom, services);

        // limit observers
        final Pair<JTerm, ImmutableSet<Taclet>> limited =
            limitTerm(schemaAxiom.term, toLimit, services);
        final JTerm limitedAxiom = limited.first;
        result = result.union(limited.second);

        // create added sequent
        final SequentFormula addedCf = new SequentFormula(limitedAxiom);
        final Sequent addedSeq =
            JavaDLSequentKit.createAnteSequent(ImmutableList.singleton(addedCf));

        final JTerm[] hs = new JTerm[heapSVs.size()];
        i = 0;
        for (var heapSV : heapSVs) {
            hs[i++] = TB.var(heapSV);
        }
        // create taclet
        final AntecTacletBuilder tacletBuilder = new AntecTacletBuilder();
        final JTerm invTerm;
        if (isStatic && isFree) {
            invTerm = TB.staticInvFree(hs, kjt);
        } else if (isStatic) {
            invTerm = TB.staticInv(hs, kjt);
        } else if (isFree) {
            invTerm = TB.invFree(hs, eqVersion ? TB.var(eqSV) : TB.var(selfSV));
        } else {
            invTerm = TB.inv(hs, eqVersion ? TB.var(eqSV) : TB.var(selfSV));
        }

        tacletBuilder.setFind(invTerm);
        tacletBuilder.addTacletGoalTemplate(
            new TacletGoalTemplate(addedSeq, ImmutableList.nil()));
        tacletBuilder.setName(name);
        tacletBuilder.addRuleSet(new RuleSet(new Name("partialInvAxiom")));
        for (VariableSV boundSV : schemaAxiom.boundVars) {
            for (SchemaVariable heapSV : heapSVs) {
                tacletBuilder.addVarsNotFreeIn(boundSV, heapSV);
            }
            if (selfSV != null) {
                tacletBuilder.addVarsNotFreeIn(boundSV, selfSV);
            }
            if (eqSV != null && eqVersion) {
                tacletBuilder.addVarsNotFreeIn(boundSV, eqSV);
            }
        }

        if (eqVersion) {
            assert !isStatic;
            // \assumes( self = EQ ==> EQ = null )
            final JTerm selfEQ = TB.equals(TB.var(selfSV), TB.var(eqSV));
            final JTerm eqNull = TB.equals(TB.var(eqSV), TB.NULL());
            final SequentFormula selfEQSF = new SequentFormula(selfEQ);
            final SequentFormula eqNullSF = new SequentFormula(eqNull);
            final var antec =
                ImmutableList.singleton(selfEQSF);
            final var succ =
                ImmutableList.singleton(eqNullSF);
            final Sequent ifSeq = JavaDLSequentKit.createSequent(antec, succ);
            tacletBuilder.setAssumesSequent(ifSeq);
        } else if (!isStatic) {
            // \assumes( ==> self = null )
            final JTerm selfNull = TB.equals(TB.var(selfSV), TB.NULL());
            final SequentFormula selfNullSF = new SequentFormula(selfNull);
            final Sequent ifSeq =
                JavaDLSequentKit.createSuccSequent(ImmutableList.singleton(selfNullSF));
            tacletBuilder.setAssumesSequent(ifSeq);
        }

        result = result.add(tacletBuilder.getTaclet());
        return result;
    }


    @SuppressWarnings("unused")
    private TermAndBoundVarPair createSchemaTerm(JTerm term, TermServices services,
            Pair<LocationVariable, JOperatorSV>... varPairs) {
        ImmutableList<@Nullable LocationVariable> progVars = ImmutableList.nil();
        ImmutableList<@Nullable JOperatorSV> schemaVars = ImmutableList.nil();
        for (Pair<LocationVariable, JOperatorSV> varPair : varPairs) {
            progVars = progVars.append(varPair.first);
            schemaVars = schemaVars.append(varPair.second);
        }
        return createSchemaTerm(term, progVars, schemaVars, services);
    }


    private TermAndBoundVarPair createSchemaTerm(JTerm term,
            ImmutableList<@Nullable LocationVariable> programVars,
            ImmutableList<@Nullable JOperatorSV> schemaVars,
            TermServices services) {
        final OpReplacer or = createOpReplacer(programVars, schemaVars, services);
        final JTerm rawTerm =
            Objects.requireNonNull(or.replace(term), "no replacement result for " + term);
        final TermAndBoundVarPair schemaTerm = replaceBoundLogicVars(rawTerm, services);
        return schemaTerm;
    }


    private @Nullable TermSV createSchemaVariable(@Nullable ProgramVariable programVar) {
        if (programVar == null) {
            return null;
        } else {
            Name name = new Name("sv_" + programVar.name());
            var schemaVar = SchemaVariableFactory.createTermSV(name,
                Objects.requireNonNull(
                    Objects.requireNonNull(programVar.getKeYJavaType(),
                        "no KeYJavaType for " + programVar).getSort(),
                    "no sort for " + programVar));
            return schemaVar;
        }
    }


    private ImmutableList<JOperatorSV> createSchemaVariables(
            ImmutableList<LocationVariable> programVars) {
        ImmutableList<JOperatorSV> schemaVars = ImmutableList.nil();
        for (LocationVariable progVar : programVars) {
            JOperatorSV schemaVar = Objects.requireNonNull(createSchemaVariable(progVar),
                "no schema variable for " + progVar);
            schemaVars = schemaVars.append(schemaVar);
        }
        return schemaVars;
    }


    private ImmutableList<@Nullable LocationVariable> widenProgramVars(
            ImmutableList<LocationVariable> programVars) {
        ImmutableList<@Nullable LocationVariable> widened = ImmutableList.nil();
        for (LocationVariable progVar : programVars) {
            widened = widened.append(progVar);
        }
        return widened;
    }


    private ImmutableList<@Nullable JOperatorSV> widenSchemaVars(
            ImmutableList<JOperatorSV> schemaVars) {
        ImmutableList<@Nullable JOperatorSV> widened = ImmutableList.nil();
        for (JOperatorSV schemaVar : schemaVars) {
            widened = widened.append(schemaVar);
        }
        return widened;
    }


    /**
     * Creates a term without term labels. {@link TermFactory#createTerm} declares the labels
     * argument {@code @NonNull} although its implementation treats {@code null} as "no labels".
     */
    @SuppressWarnings({ "NullAway", "nullness:argument.type.incompatible" })
    private JTerm createTermWithoutLabels(TermFactory tf, Operator op, JTerm[] subs,
            @Nullable ImmutableArray<QuantifiableVariable> boundVars) {
        return tf.createTerm(op, subs, boundVars, null);
    }


    /**
     * Creates a statement block without execution context. {@link ContextStatementBlock} keeps
     * its context field nullable in practice and null-guards all accessors, although its
     * constructor declares the argument {@code @NonNull}.
     */
    @SuppressWarnings({ "NullAway", "nullness:argument.type.incompatible" })
    private ContextStatementBlock contextStatementBlock(Statement s) {
        return new ContextStatementBlock(s, null);
    }


    private OpReplacer createOpReplacer(ImmutableList<@Nullable LocationVariable> programVars,
            ImmutableList<@Nullable JOperatorSV> schemaVars, TermServices services) {
        assert programVars.size() == schemaVars.size();
        final Map<LocationVariable, JOperatorSV> map =
            new LinkedHashMap<>();
        Iterator<@Nullable JOperatorSV> schemaIt = schemaVars.iterator();
        for (@Nullable
        LocationVariable progVar : programVars) {
            @Nullable
            JOperatorSV schemaVar = schemaIt.next();
            if (progVar != null) {
                // programVars and schemaVars are appended pairwise, so a non-null program
                // variable always has a non-null schema variable counterpart (null self entries
                // are skipped here).
                map.put(progVar, Objects.requireNonNull(schemaVar,
                    "no schema variable for " + progVar));
            }
        }
        return new OpReplacer(map, services.getTermFactory());
    }


    /**
     * Replaces any bound logical variables in t with schema variables (necessary for proof
     * saving/loading, if t occurs as part of a taclet).
     *
     * @param services TODO
     */
    private TermAndBoundVarPair replaceBoundLogicVars(JTerm t, TermServices services) {
        // recursive replacement process
        final TermAndBoundVarPair intermediateRes = replaceBoundLVsWithSVsHelper(t, services);

        // Post-processing: different bound variables with the same name
        // (but non-overlapping scopes) may be used in t; in contrast, the
        // schema variables in this method's result must have names that are
        // unique within the term.

        // collect all operator names used in t
        final OpCollector oc = new OpCollector();
        oc.visit(t);
        final Set<Name> usedNames = new LinkedHashSet<>();
        for (final var op : oc.ops()) {
            usedNames.add(op.name());
        }

        // find and resolve name conflicts between schema variables
        ImmutableSet<VariableSV> newSVs = DefaultImmutableSet.nil();
        final Set<Name> namesOfNewSVs = new LinkedHashSet<>();
        final Map<VariableSV, VariableSV> replaceMap = new LinkedHashMap<>();
        for (VariableSV sv : intermediateRes.boundVars) {
            if (namesOfNewSVs.contains(sv.name())) {
                // choose alternative name
                final String baseName = sv.name().toString();
                int i = 0;
                Name newName;
                do {
                    newName = new Name(baseName + "_" + i++);
                } while (usedNames.contains(newName));

                // create new SV, register in replace map
                final VariableSV newSV = SchemaVariableFactory.createVariableSV(newName, sv.sort());
                newSVs = newSVs.add(newSV);
                namesOfNewSVs.add(newSV.name());
                usedNames.add(newSV.name());
                replaceMap.put(sv, newSV);
            } else {
                newSVs = newSVs.add(sv);
                namesOfNewSVs.add(sv.name());
            }
        }
        final OpReplacer or = new OpReplacer(replaceMap, services.getTermFactory());
        final JTerm newTerm = Objects.requireNonNull(or.replace(intermediateRes.term),
            "no replacement result for " + intermediateRes.term);

        return new TermAndBoundVarPair(newTerm, newSVs);
    }


    private TermAndBoundVarPair replaceBoundLVsWithSVsHelper(JTerm t, TermServices services) {
        ImmutableSet<VariableSV> svs = DefaultImmutableSet.nil();

        // prepare op replacer, new bound vars
        final Map<Operator, Operator> map = new LinkedHashMap<>();
        final ImmutableArray<QuantifiableVariable> boundVars = t.boundVars();
        final QuantifiableVariable[] newBoundVars = new QuantifiableVariable[boundVars.size()];
        for (int i = 0; i < newBoundVars.length; i++) {
            final QuantifiableVariable qv = boundVars.get(i);
            if (qv instanceof LogicVariable) {
                final VariableSV sv = SchemaVariableFactory.createVariableSV(qv.name(), qv.sort());
                svs = svs.add(sv);
                newBoundVars[i] = sv;
                map.put(qv, sv);
            } else {
                newBoundVars[i] = qv;
            }
        }
        final OpReplacer or = new OpReplacer(map, services.getTermFactory());

        // handle subterms
        final JTerm[] newSubs = new JTerm[t.arity()];
        boolean changedSub = false;
        for (int i = 0; i < newSubs.length; i++) {
            if (t.op().bindVarsAt(i)) {
                newSubs[i] = Objects.requireNonNull(or.replace(t.sub(i)),
                    "no replacement result for " + t.sub(i));
            } else {
                newSubs[i] = t.sub(i);
            }
            final TermAndBoundVarPair subPair = replaceBoundLVsWithSVsHelper(newSubs[i], services);
            newSubs[i] = subPair.term;
            svs = svs.union(subPair.boundVars);
            if (newSubs[i] != t.sub(i)) {
                changedSub = true;
            }
        }

        // build overall term
        final JTerm newTerm;
        if (map.isEmpty() && !changedSub) {
            newTerm = t;
        } else {
            newTerm = createTermWithoutLabels(services.getTermBuilder().tf(), t.op(), newSubs,
                new ImmutableArray<>(newBoundVars));
        }

        return new TermAndBoundVarPair(newTerm, svs);
    }


    private Pair<JTerm, ImmutableSet<Taclet>> limitTerm(JTerm t,
            ImmutableSet<Pair<Sort, IObserverFunction>> toLimit, Services services) {
        ImmutableSet<Taclet> taclets = DefaultImmutableSet.nil();

        // recurse to subterms
        JTerm[] subs = new JTerm[t.arity()];
        for (int i = 0; i < subs.length; i++) {
            Pair<JTerm, ImmutableSet<Taclet>> pair = limitTerm(t.sub(i), toLimit, services);
            subs[i] = pair.first;
            taclets = taclets.union(pair.second);
        }

        // top level operator
        Operator newOp = t.op();
        if (t.op() instanceof IObserverFunction obs) {
            for (Pair<Sort, IObserverFunction> pair : toLimit) {
                if (pair.second.equals(t.op())
                        && (obs.isStatic() || t.sub(1).sort().extendsTrans(pair.first))) {
                    Pair<IObserverFunction, ImmutableSet<Taclet>> limited =
                        services.getSpecificationRepository().limitObs(obs);
                    newOp = limited.first;
                    taclets = taclets.union(limited.second);
                }
            }
        }

        // reassemble, return
        final JTerm term = createTermWithoutLabels(services.getTermBuilder().tf(), newOp, subs,
            t.boundVars());
        return new Pair<>(term, taclets);
    }


    private SequentFormula generateGuard(KeYJavaType kjt, IObserverFunction target,
            TermServices services, final @Nullable JOperatorSV selfSV, List<TermSV> heapSVs,
            ImmutableList<JOperatorSV> paramSVs, final JTerm schemaAxiom,
            final RewriteTacletBuilder<? extends RewriteTaclet> tacletBuilder, boolean addGuard) {
        final TermBuilder TB = services.getTermBuilder();
        final JTerm exactInstance = prepareExactInstanceGuard(kjt, target, services, selfSV);
        final JTerm axiomSatisfiable = addGuard
                ? prepareSatisfiabilityGuard(target, heapSVs, selfSV, paramSVs, schemaAxiom,
                    tacletBuilder, services)
                : TB.tt();
        // assemble formula
        final JTerm guardedAxiom = TB.imp(TB.and(exactInstance, axiomSatisfiable), schemaAxiom);
        final SequentFormula guardedAxiomCf = new SequentFormula(guardedAxiom);
        return guardedAxiomCf;
    }


    private JTerm prepareSatisfiabilityGuard(IObserverFunction target, List<TermSV> heapSVs,
            final @Nullable JOperatorSV selfSV, ImmutableList<JOperatorSV> paramSVs,
            final JTerm schemaAxiom,
            final RewriteTacletBuilder<? extends RewriteTaclet> tacletBuilder,
            TermServices services) {

        final TermBuilder TB = services.getTermBuilder();
        ImmutableList<JTerm> vars = ImmutableList.nil();
        for (TermSV heapSV : heapSVs) {
            vars = vars.append(TB.var(heapSV));
        }
        if (!target.isStatic()) {
            vars = vars.append(TB.var(Objects.requireNonNull(selfSV,
                "no self schema variable for " + target)));
        }
        for (var sv : paramSVs) {
            vars = vars.append(TB.var(sv));
        }
        final JTerm targetTerm = TB.func(target, vars.toArray(new JTerm[0]));

        final JTerm axiomSatisfiable;
        if (target.sort() == JavaDLTheory.FORMULA) {
            axiomSatisfiable = TB.or(
                OpReplacer.replace(targetTerm, TB.tt(), schemaAxiom, services.getTermFactory()),
                OpReplacer.replace(targetTerm, TB.ff(), schemaAxiom, services.getTermFactory()));
        } else {
            final VariableSV targetSV = SchemaVariableFactory.createVariableSV(
                new Name(target.sort().name().toString().charAt(0) + "_lv"), target.sort());
            for (SchemaVariable heapSV : heapSVs) {
                tacletBuilder.addVarsNotFreeIn(targetSV, heapSV);
            }
            if (!target.isStatic()) {
                tacletBuilder.addVarsNotFreeIn(targetSV, Objects.requireNonNull(selfSV,
                    "no self schema variable for " + target));
            }

            for (var paramSV : paramSVs) {
                tacletBuilder.addVarsNotFreeIn(targetSV, paramSV);
            }
            JTerm targetLVReachable = null;
            for (var heapSV : heapSVs) {
                final JTerm targetReachable =
                    TB.reachableValue(TB.var(heapSV), TB.var(targetSV),
                        Objects.requireNonNull(target.getType(), "no result type of " + target));
                if (targetLVReachable == null) {
                    targetLVReachable = targetReachable;
                } else {
                    targetLVReachable = TB.and(targetLVReachable, targetReachable);
                }
            }

            axiomSatisfiable = TB.ex(targetSV,
                TB.and(Objects.requireNonNull(targetLVReachable,
                    "no reachability term for " + target),
                    OpReplacer.replace(targetTerm, TB.var(targetSV), schemaAxiom,
                        services.getTermFactory())));
        }
        return axiomSatisfiable;
    }


    private JTerm prepareExactInstanceGuard(KeYJavaType kjt, IObserverFunction target,
            TermServices services, final @Nullable JOperatorSV selfSV) {
        final boolean finalClass = kjt.getJavaType() instanceof ClassDeclaration
                && ((ClassDeclaration) kjt.getJavaType()).isFinal();
        // TODO: exact instance necessary?
        // or better: instance(finalClass, selfSV, services)?
        final TermBuilder TB = services.getTermBuilder();
        final JTerm exactInstance = target.isStatic() || finalClass ? TB.tt()
                : TB.exactInstance(
                    Objects.requireNonNull(kjt.getSort(), "no sort for " + kjt),
                    TB.var(Objects.requireNonNull(selfSV,
                        "no self schema variable for " + target)));
        return exactInstance;
    }


    private record TermAndBoundVarPair(JTerm term, ImmutableSet<VariableSV> boundVars) {
    }
}
