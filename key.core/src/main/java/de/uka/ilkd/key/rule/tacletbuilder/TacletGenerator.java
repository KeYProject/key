/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.tacletbuilder;

import java.util.*;

import de.uka.ilkd.key.java.ContextStatementBlock;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.ClassDeclaration;
import de.uka.ilkd.key.java.statement.MethodBodyStatement;
import de.uka.ilkd.key.ldt.JavaDLTheory;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.op.ParsableVariable;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.sort.ProgramSVSort;
import de.uka.ilkd.key.proof.OpReplacer;
import de.uka.ilkd.key.rule.RewriteTaclet;
import de.uka.ilkd.key.rule.RuleSet;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.speclang.HeapContext;

import org.key_project.logic.Name;
import org.key_project.logic.sort.Sort;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.ImmutableSet;
import org.key_project.util.collection.Pair;



/**
 *
 * @author christoph
 */
public class TacletGenerator {

    private static final TacletGenerator instance = new TacletGenerator();


    private TacletGenerator() {
    }


    public static TacletGenerator getInstance() {
        return instance;
    }


    private TacletGoalTemplate createAxiomGoalTemplate(Term goalTerm) {
        final SequentFormula axiomSf = new SequentFormula(goalTerm);
        final Semisequent axiomSemiSeq =
            Semisequent.EMPTY_SEMISEQUENT.insertFirst(axiomSf).semisequent();
        final Sequent axiomSeq = Sequent.createAnteSequent(axiomSemiSeq);
        final TacletGoalTemplate axiomTemplate =
            new TacletGoalTemplate(axiomSeq, ImmutableSLList.nil());
        return axiomTemplate;
    }


    /**
     * Returns a no-find taclet to the passed axiom. If the axiom expression does not contain
     * reference to self, it is considered as if it were static.
     */
    public Taclet generateAxiomTaclet(Name tacletName, Term originalAxiom,
            ImmutableList<ProgramVariable> programVars, KeYJavaType kjt, RuleSet ruleSet,
            TermServices services) {
        // create schema terms
        final ImmutableList<SchemaVariable> schemaVars = createSchemaVariables(programVars);
        final TermAndBoundVarPair schemaAxiom =
            createSchemaTerm(originalAxiom, programVars, schemaVars, services);

        // create taclet
        NoFindTacletBuilder tacletBuilder = new NoFindTacletBuilder();
        tacletBuilder.setName(tacletName);
        tacletBuilder.addTacletGoalTemplate(createAxiomGoalTemplate(schemaAxiom.term));
        tacletBuilder.addVarsNotFreeIn(schemaAxiom.boundVars, schemaVars);
        tacletBuilder.addRuleSet(ruleSet);
        return tacletBuilder.getTaclet();
    }


    public Taclet generateRewriteTaclet(Name tacletName, Term originalFind, Term originalAxiom,
            ImmutableList<ProgramVariable> programVars, RuleSet ruleSet, TermServices services) {
        // create schema terms
        final ImmutableList<SchemaVariable> schemaVars = createSchemaVariables(programVars);
        final TermAndBoundVarPair schemaFind =
            createSchemaTerm(originalFind, programVars, schemaVars, services);
        final TermAndBoundVarPair schemaAxiom =
            createSchemaTerm(originalAxiom, programVars, schemaVars, services);
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


    public Taclet generateRelationalRepresentsTaclet(Name tacletName, Term originalAxiom,
            KeYJavaType kjt, IObserverFunction target, List<? extends ProgramVariable> heaps,
            ProgramVariable self, ImmutableList<ProgramVariable> paramVars,
            Map<LocationVariable, ProgramVariable> atPreVars, boolean satisfiabilityGuard,
            TermServices services) {
        final RewriteTacletBuilder<RewriteTaclet> tacletBuilder = new RewriteTacletBuilder<>();

        TermBuilder tb = services.getTermBuilder();
        originalAxiom = tb.convertToFormula(originalAxiom);

        // create schema terms
        ImmutableList<ProgramVariable> pvs = ImmutableSLList.nil();
        ImmutableList<SchemaVariable> svs = ImmutableSLList.nil();
        List<SchemaVariable> heapSVs = new ArrayList<>();
        for (ProgramVariable heap : heaps) {
            if (target.getStateCount() >= 1) {
                pvs = pvs.append(heap);
                SchemaVariable heapSV = createSchemaVariable(heap);
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

        final SchemaVariable selfSV = createSchemaVariable(self);

        ImmutableList<SchemaVariable> paramSVs = ImmutableSLList.nil();
        for (ProgramVariable paramVar : paramVars) {
            paramSVs = paramSVs.append(createSchemaVariable(paramVar));
        }
        pvs = pvs.append(self).append(paramVars);
        svs = svs.append(selfSV).append(paramSVs);

        final TermAndBoundVarPair schemaAxiom = createSchemaTerm(originalAxiom, pvs, svs, services);

        // create goal template
        SequentFormula guardedSchemaAxiom = generateGuard(kjt, target, services, selfSV, heapSVs,
            paramSVs, schemaAxiom.term, tacletBuilder, satisfiabilityGuard);
        final Sequent addedSeq = Sequent.createAnteSequent(
            Semisequent.EMPTY_SEMISEQUENT.insertFirst(guardedSchemaAxiom).semisequent());
        ImmutableList<Term> vars = ImmutableSLList.nil();
        for (SchemaVariable heapSV : heapSVs) {
            vars = vars.append(tb.var(heapSV));
        }
        if (!target.isStatic()) {
            vars = vars.append(tb.var(selfSV));
        }
        for (SchemaVariable sv : paramSVs) {
            vars = vars.append(tb.var(sv));
        }
        final Term findTerm = tb.func(target, vars.toArray(new Term[0]));

        final RewriteTacletGoalTemplate axiomTemplate =
            new RewriteTacletGoalTemplate(addedSeq, ImmutableSLList.nil(), findTerm);

        // choices, rule set
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
        for (SchemaVariable heapSV : heapSVs) {
            tacletBuilder.addVarsNotFreeIn(schemaAxiom.boundVars, heapSV);
        }
        for (SchemaVariable paramSV : paramSVs) {
            tacletBuilder.addVarsNotFreeIn(schemaAxiom.boundVars, paramSV);
        }

        tacletBuilder.addRuleSet(ruleSet);
        return tacletBuilder.getTaclet();
    }


    public ImmutableSet<Taclet> generateFunctionalRepresentsTaclets(Name name, Term originalPreTerm,
            Term originalRepresentsTerm, KeYJavaType kjt, IObserverFunction target,
            List<? extends ProgramVariable> heaps, ProgramVariable self,
            ImmutableList<ProgramVariable> paramVars,
            Map<LocationVariable, ProgramVariable> atPreVars,
            ImmutableSet<Pair<Sort, IObserverFunction>> toLimit, boolean satisfiability,
            Services services) {
        ImmutableSet<Taclet> result = DefaultImmutableSet.nil();
        TermBuilder TB = services.getTermBuilder();

        // instantiate axiom with schema variables
        ImmutableList<ProgramVariable> pvs = ImmutableSLList.nil();
        ImmutableList<SchemaVariable> svs = ImmutableSLList.nil();
        List<SchemaVariable> heapSVs = new ArrayList<>();
        for (ProgramVariable heap : heaps) {
            if (target.getStateCount() >= 1) {
                pvs = pvs.append(heap);
                SchemaVariable heapSV = createSchemaVariable(heap);
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

        final SchemaVariable selfSV = createSchemaVariable(self);
        ImmutableList<SchemaVariable> paramSVs = ImmutableSLList.nil();
        for (ProgramVariable paramVar : paramVars) {
            paramSVs = paramSVs.append(createSchemaVariable(paramVar));
        }
        pvs = pvs.append(self).append(paramVars);
        svs = svs.append(selfSV).append(paramSVs);
        final TermAndBoundVarPair schemaRepresents =
            createSchemaTerm(originalRepresentsTerm, pvs, svs, services);
        assert schemaRepresents.term.op() instanceof Equality;
        final Term schemaLhs = schemaRepresents.term.sub(0);
        final Term schemaRhs = schemaRepresents.term.sub(1);

        // limit observers
        final Pair<Term, ImmutableSet<Taclet>> limited = limitTerm(schemaRhs, toLimit, services);
        final Term limitedRhs = limited.first;
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
            final Term ifFormula = TB.equals(TB.var(selfSV), TB.NULL());
            final SequentFormula ifCf = new SequentFormula(ifFormula);
            final Semisequent ifSemiSeq =
                Semisequent.EMPTY_SEMISEQUENT.insertFirst(ifCf).semisequent();
            ifSeq = Sequent.createSuccSequent(ifSemiSeq);
        } else {
            /* \assumes ( Sort.exactInstance(self) ==> ) */
            final Term ifFormula = TB.exactInstance(kjt.getSort(), TB.var(selfSV));
            final SequentFormula ifCf = new SequentFormula(ifFormula);
            final Semisequent ifSemiSeq =
                Semisequent.EMPTY_SEMISEQUENT.insertFirst(ifCf).semisequent();
            ifSeq = Sequent.createAnteSequent(ifSemiSeq);
        }

        Term addForumlaTerm = originalPreTerm;
        // The presence of the precondition term means we are dealing with a model method definition
        // taclet, an \add section to check preconditions has to be added
        // FIXME does this also affect the satisfiability branches?
        if (addForumlaTerm != null) {
            Term wfFormula = null;
            Term createdFormula = null;
            for (SchemaVariable heapSV : heapSVs) {
                final Term wf = TB.wellFormed(TB.var(heapSV));
                if (wfFormula == null) {
                    wfFormula = wf;
                } else {
                    wfFormula = TB.and(wfFormula, wf);
                }
                if (!target.isStatic()) {
                    final Term crf = TB.created(TB.var(heapSV), TB.var(selfSV));
                    if (createdFormula == null) {
                        createdFormula = crf;
                    } else {
                        createdFormula = TB.and(createdFormula, crf);
                    }
                }
            }
            final Term selfNull = target.isStatic() ? null : TB.equals(TB.var(selfSV), TB.NULL());
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
        tacletBuilder.addTacletGoalTemplate(new RewriteTacletGoalTemplate(Sequent.EMPTY_SEQUENT,
            ImmutableSLList.nil(), limitedRhs));

        // FIXME - there is a chance this will have to go along with all the other associated
        // changes
        /*
         * if(addedSeq != null) { TacletGoalTemplate tgc = new TacletGoalTemplate(addedSeq,
         * ImmutableSLList.<Taclet>nil()); tgc.setName("Precondition of "+target.name());
         * tacletBuilder.addTacletGoalTemplate (tgc); }
         */
        if (ifSeq != null) {
            tacletBuilder.setIfSequent(ifSeq);
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
        tacletBuilder.setApplicationRestriction(RewriteTaclet.SAME_UPDATE_LEVEL);
        result = result.add(tacletBuilder.getTaclet());
        // return
        return result;
    }


    private void functionalRepresentsAddSatisfiabilityBranch(IObserverFunction target,
            TermServices services, List<SchemaVariable> heapSVs, final SchemaVariable selfSV,
            ImmutableList<SchemaVariable> paramSVs, final TermAndBoundVarPair schemaRepresents,
            final RewriteTacletBuilder<? extends RewriteTaclet> tacletBuilder) {
        final Term axiomSatisfiable = functionalRepresentsSatisfiability(target, services, heapSVs,
            selfSV, paramSVs, schemaRepresents, tacletBuilder);
        SequentFormula addedCf = new SequentFormula(axiomSatisfiable);
        final Semisequent addedSemiSeq =
            Semisequent.EMPTY_SEMISEQUENT.insertFirst(addedCf).semisequent();
        final Sequent addedSeq = Sequent.createSuccSequent(addedSemiSeq);
        final SchemaVariable skolemSV =
            SchemaVariableFactory.createSkolemTermSV(new Name("sk"), target.sort());
        for (SchemaVariable heapSV : heapSVs) {
            tacletBuilder.addVarsNewDependingOn(skolemSV, heapSV);
        }
        if (!target.isStatic()) {
            tacletBuilder.addVarsNewDependingOn(skolemSV, selfSV);
        }
        for (SchemaVariable paramSV : paramSVs) {
            tacletBuilder.addVarsNewDependingOn(skolemSV, paramSV);
        }
        tacletBuilder.addTacletGoalTemplate(new RewriteTacletGoalTemplate(addedSeq,
            ImmutableSLList.nil(), services.getTermBuilder().var(skolemSV)));
        tacletBuilder.goalTemplates().tail().head().setName("Use Axiom");
        tacletBuilder.goalTemplates().head().setName("Show Axiom Satisfiability");
    }


    private Term functionalRepresentsSatisfiability(IObserverFunction target, TermServices services,
            List<SchemaVariable> heapSVs, final SchemaVariable selfSV,
            ImmutableList<SchemaVariable> paramSVs, final TermAndBoundVarPair schemaRepresents,
            final RewriteTacletBuilder<? extends RewriteTaclet> tacletBuilder) {
        ImmutableList<Term> vars = ImmutableSLList.nil();
        TermBuilder TB = services.getTermBuilder();
        for (SchemaVariable heapSV : heapSVs) {
            vars = vars.append(TB.var(heapSV));
        }
        if (!target.isStatic()) {
            vars = vars.append(TB.var(selfSV));
        }
        for (SchemaVariable sv : paramSVs) {
            vars = vars.append(TB.var(sv));
        }
        final Term targetTerm = TB.func(target, vars.toArray(new Term[0]));

        final Term axiomSatisfiable;
        if (target.sort() == JavaDLTheory.FORMULA) {
            axiomSatisfiable = TB.or(
                OpReplacer.replace(targetTerm, TB.tt(), schemaRepresents.term,
                    services.getTermFactory()),
                OpReplacer.replace(targetTerm, TB.ff(), schemaRepresents.term,
                    services.getTermFactory()));
        } else {
            final VariableSV targetSV = SchemaVariableFactory.createVariableSV(
                new Name(target.sort().name().toString().substring(0, 1)), target.sort());
            Term targetSVReachable = null;
            for (SchemaVariable heapSV : heapSVs) {
                tacletBuilder.addVarsNotFreeIn(targetSV, heapSV);
                final Term tReach =
                    TB.reachableValue(TB.var(heapSV), TB.var(targetSV), target.getType());
                if (targetSVReachable == null) {
                    targetSVReachable = tReach;
                } else {
                    targetSVReachable = TB.and(targetSVReachable, tReach);
                }
            }
            if (!target.isStatic()) {
                tacletBuilder.addVarsNotFreeIn(targetSV, selfSV);
            }
            for (SchemaVariable paramSV : paramSVs) {
                tacletBuilder.addVarsNotFreeIn(targetSV, paramSV);
            }
            axiomSatisfiable =
                TB.ex(targetSV, TB.and(targetSVReachable, OpReplacer.replace(targetTerm,
                    TB.var(targetSV), schemaRepresents.term, services.getTermFactory())));
        }
        return axiomSatisfiable;
    }

    public ImmutableSet<Taclet> generateContractAxiomTaclets(Name name, Term originalPre,
            Term originalFreePre, Term originalPost, Term originalFreePost, Term originalMby,
            KeYJavaType kjt, IObserverFunction target, List<? extends ProgramVariable> heaps,
            ProgramVariable originalSelfVar, ProgramVariable originalResultVar,
            Map<LocationVariable, ProgramVariable> atPreVars,
            ImmutableList<ProgramVariable> originalParamVars,
            ImmutableSet<Pair<Sort, IObserverFunction>> toLimit, boolean satisfiabilityGuard,
            TermServices services) {

        ImmutableList<ProgramVariable> pvs = ImmutableSLList.nil();
        ImmutableList<SchemaVariable> svs = ImmutableSLList.nil();
        final List<SchemaVariable> heapSVs = new ArrayList<>();
        for (ProgramVariable heap : heaps) {
            if (target.getStateCount() >= 1) {
                pvs = pvs.append(heap);
                SchemaVariable sv = SchemaVariableFactory.createTermSV(
                    new Name("sv_" + heap.name().toString()), heap.sort(), false, false);
                svs = svs.append(sv);
                heapSVs.add(sv);
                if (target.getStateCount() == 2) {
                    pvs = pvs.append(atPreVars.get(heap));
                    sv = SchemaVariableFactory.createTermSV(
                        new Name("sv_" + atPreVars.get(heap).name().toString()), heap.sort(), false,
                        false);
                    svs = svs.append(sv);
                    heapSVs.add(sv);
                }
            }
        }
        final SchemaVariable selfSV = target.isStatic() ? null
                : SchemaVariableFactory.createTermSV(new Name("sv_self"), kjt.getSort(), false,
                    false);
        final SchemaVariable[] paramSVs = new SchemaVariable[target.getNumParams()];
        for (int i = 0; i < paramSVs.length; i++) {
            paramSVs[i] = SchemaVariableFactory.createTermSV(new Name("sv_p" + i),
                target.getParamType(i).getSort(), false, false);
        }
        // final SchemaVariable resultSV = SchemaVariableFactory.createTermSV(new Name("sv_r"),
        // target.getType().getSort(), false, false);

        final RewriteTacletBuilder<RewriteTaclet> tacletBuilder = new RewriteTacletBuilder<>();

        Term wfFormula = null;
        Term createdFormula = null;
        TermBuilder TB = services.getTermBuilder();
        for (SchemaVariable heapSV : heapSVs) {
            final Term wf = TB.wellFormed(TB.var(heapSV));
            if (wfFormula == null) {
                wfFormula = wf;
            } else {
                wfFormula = TB.and(wfFormula, wf);
            }
            if (!target.isStatic()) {
                final Term crf = TB.created(TB.var(heapSV), TB.var(selfSV));
                if (createdFormula == null) {
                    createdFormula = crf;
                } else {
                    createdFormula = TB.and(createdFormula, crf);
                }
            }
        }
        final Term selfNull = target.isStatic() ? null : TB.equals(TB.var(selfSV), TB.NULL());
        final Term mbyOK = originalMby != null ? TB.measuredByCheck(originalMby) : null;

        // create find
        final Term[] subs = new Term[target.arity()];
        int i = 0;
        for (SchemaVariable heapSV : heapSVs) {
            subs[i++] = TB.var(heapSV);
        }
        if (!target.isStatic()) {
            subs[i++] = TB.var(selfSV);
        }
        for (int j = 0; j < paramSVs.length; j++) {
            subs[j + i] = TB.var(paramSVs[j]);
        }
        final Term find = TB.func(target, subs);

        // build taclet
        Term addFormulaTerm = originalPre;
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

        pvs = pvs.append(originalSelfVar).append(originalParamVars); // .append(originalResultVar)
        svs = svs.append(selfSV).append(paramSVs); // .append(resultSV)
        final TermAndBoundVarPair schemaAdd = createSchemaTerm(
            TB.imp(addFormulaTerm,
                OpReplacer.replace(TB.var(originalResultVar), find,
                    TB.and(originalPost, originalFreePost), services.getTermFactory())),
            pvs, svs, services);

        final Term addedFormula = schemaAdd.term;
        final SequentFormula addedCf = new SequentFormula(addedFormula);
        final Semisequent addedSemiSeq =
            Semisequent.EMPTY_SEMISEQUENT.insertFirst(addedCf).semisequent();
        final Sequent addedSeq = Sequent.createAnteSequent(addedSemiSeq);

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
        tacletBuilder.setApplicationRestriction(RewriteTaclet.SAME_UPDATE_LEVEL);
        tacletBuilder.addTacletGoalTemplate(
            new TacletGoalTemplate(addedSeq, ImmutableSLList.nil()));
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

        final ImmutableList<KeYJavaType> sig = ImmutableSLList.<KeYJavaType>nil()
                .append(target.getParamTypes().toArray(new KeYJavaType[target.getNumParams()]));
        final IProgramMethod targetImpl = services.getJavaInfo().getProgramMethod(kjt,
            ((ProgramMethod) target).getName(), sig, kjt);

        final MethodBodyStatement mbs = new MethodBodyStatement(targetImpl, selfProgSV,
            resultProgSV, new ImmutableArray<>(paramProgSVs));
        final JavaBlock findBlock = JavaBlock.createJavaBlock(new ContextStatementBlock(mbs, null));

        final var modalitySV =
            SchemaVariableFactory.createModalOperatorSV(new Name("#allModal_sv"),
                JavaDLTheory.FORMULA,
                DefaultImmutableSet.<Modality.JavaModalityKind>nil()
                        .add(Modality.JavaModalityKind.DIA)
                        .add(Modality.JavaModalityKind.BOX)
                        .add(Modality.JavaModalityKind.DIA_TRANSACTION)
                        .add(Modality.JavaModalityKind.BOX_TRANSACTION));
        SchemaVariable postSV = SchemaVariableFactory.createFormulaSV(new Name("#post_sv"));

        final Term findTerm =
            TB.tf().createTerm(Modality.getModality(modalitySV, findBlock),
                new Term[] { TB.var(postSV) }, null, null);

        final JavaBlock replaceBlock =
            JavaBlock.createJavaBlock(new ContextStatementBlock(new StatementBlock(), null));

        final Term[] updateSubs = new Term[target.arity()];
        int i = 0;
        updateSubs[i++] = TB.var(services.getTypeConverter().getHeapLDT().getHeap());
        if (target.getStateCount() == 2) {
            updateSubs[i++] = TB.var(services.getTypeConverter().getHeapLDT().getHeap());
        }
        if (!target.isStatic()) {
            updateSubs[i++] = TB.var(selfProgSV);
        }
        for (int j = 0; j < paramProgSVs.length; j++) {
            updateSubs[j + i] = TB.var(paramProgSVs[j]);
        }

        final Term replaceTerm =
            TB.apply(TB.elementary(TB.var(resultProgSV), TB.func(target, updateSubs)),
                TB.tf().createTerm(Modality.getModality(modalitySV, replaceBlock),
                    new Term[] { TB.var(postSV) }, null, null));

        final RewriteTacletBuilder<RewriteTaclet> replaceTacletBuilder =
            new RewriteTacletBuilder<>();

        replaceTacletBuilder.setFind(findTerm);
        replaceTacletBuilder.setApplicationRestriction(RewriteTaclet.SAME_UPDATE_LEVEL);
        replaceTacletBuilder.addTacletGoalTemplate(new RewriteTacletGoalTemplate(replaceTerm));
        replaceTacletBuilder.setName(name);
        replaceTacletBuilder.addRuleSet(new RuleSet(new Name("simplify_prog"))); // TODO ?

        return DefaultImmutableSet.<Taclet>nil().add(replaceTacletBuilder.getTaclet());

    }


    public ImmutableSet<Taclet> generatePartialInvTaclet(Name name, List<SchemaVariable> heapSVs,
            SchemaVariable selfSV, SchemaVariable eqSV, Term term, KeYJavaType kjt,
            ImmutableSet<Pair<Sort, IObserverFunction>> toLimit, boolean isStatic, boolean isFree,
            boolean eqVersion, Services services) {
        TermBuilder TB = services.getTermBuilder();
        ImmutableSet<Taclet> result = DefaultImmutableSet.nil();
        Map<Term, Term> replace = new LinkedHashMap<>();
        int i = 0;
        for (ProgramVariable heap : HeapContext.getModHeaps(services, false)) {
            replace.put(TB.var(heap), TB.var(heapSVs.get(i++)));
        }
        final OpReplacer replacer = new OpReplacer(replace, services.getTermFactory());
        // TB.getBaseHeap(services), TB.var(heapSV)
        // instantiate axiom with schema variables
        final Term rawAxiom = replacer.replace(term);
        final TermAndBoundVarPair schemaAxiom = replaceBoundLogicVars(rawAxiom, services);

        // limit observers
        final Pair<Term, ImmutableSet<Taclet>> limited =
            limitTerm(schemaAxiom.term, toLimit, services);
        final Term limitedAxiom = limited.first;
        result = result.union(limited.second);

        // create added sequent
        final SequentFormula addedCf = new SequentFormula(limitedAxiom);
        final Semisequent addedSemiSeq =
            Semisequent.EMPTY_SEMISEQUENT.insertFirst(addedCf).semisequent();
        final Sequent addedSeq = Sequent.createAnteSequent(addedSemiSeq);

        final Term[] hs = new Term[heapSVs.size()];
        i = 0;
        for (SchemaVariable heapSV : heapSVs) {
            hs[i++] = TB.var(heapSV);
        }
        // create taclet
        final AntecTacletBuilder tacletBuilder = new AntecTacletBuilder();
        final Term invTerm;
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
            new TacletGoalTemplate(addedSeq, ImmutableSLList.nil()));
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
            final Term selfEQ = TB.equals(TB.var(selfSV), TB.var(eqSV));
            final Term eqNull = TB.equals(TB.var(eqSV), TB.NULL());
            final SequentFormula selfEQSF = new SequentFormula(selfEQ);
            final SequentFormula eqNullSF = new SequentFormula(eqNull);
            final Semisequent succ =
                Semisequent.EMPTY_SEMISEQUENT.insertFirst(selfEQSF).semisequent();
            final Semisequent ant =
                Semisequent.EMPTY_SEMISEQUENT.insertFirst(eqNullSF).semisequent();
            final Sequent ifSeq = Sequent.createSequent(succ, ant);
            tacletBuilder.setIfSequent(ifSeq);
        } else if (!isStatic) {
            // \assumes( ==> self = null )
            final Term selfNull = TB.equals(TB.var(selfSV), TB.NULL());
            final SequentFormula selfNullSF = new SequentFormula(selfNull);
            final Semisequent succ =
                Semisequent.EMPTY_SEMISEQUENT.insertFirst(selfNullSF).semisequent();
            final Sequent ifSeq = Sequent.createSuccSequent(succ);
            tacletBuilder.setIfSequent(ifSeq);
        }

        result = result.add(tacletBuilder.getTaclet());
        return result;
    }


    @SuppressWarnings("unused")
    private TermAndBoundVarPair createSchemaTerm(Term term, TermServices services,
            Pair<ProgramVariable, SchemaVariable>... varPairs) {
        ImmutableList<ProgramVariable> progVars = ImmutableSLList.nil();
        ImmutableList<SchemaVariable> schemaVars = ImmutableSLList.nil();
        for (Pair<ProgramVariable, SchemaVariable> varPair : varPairs) {
            progVars = progVars.append(varPair.first);
            schemaVars = schemaVars.append(varPair.second);
        }
        return createSchemaTerm(term, progVars, schemaVars, services);
    }


    private TermAndBoundVarPair createSchemaTerm(Term term,
            ImmutableList<ProgramVariable> programVars, ImmutableList<SchemaVariable> schemaVars,
            TermServices services) {
        final OpReplacer or = createOpReplacer(programVars, schemaVars, services);
        final Term rawTerm = or.replace(term);
        final TermAndBoundVarPair schemaTerm = replaceBoundLogicVars(rawTerm, services);
        return schemaTerm;
    }


    private SchemaVariable createSchemaVariable(ProgramVariable programVar) {
        if (programVar == null) {
            return null;
        } else {
            Name name = new Name("sv_" + programVar.name().toString());
            SchemaVariable schemaVar =
                SchemaVariableFactory.createTermSV(name, programVar.getKeYJavaType().getSort());
            return schemaVar;
        }
    }


    private ImmutableList<SchemaVariable> createSchemaVariables(
            ImmutableList<ProgramVariable> programVars) {
        ImmutableList<SchemaVariable> schemaVars = ImmutableSLList.nil();
        for (ProgramVariable progVar : programVars) {
            SchemaVariable schemaVar = createSchemaVariable(progVar);
            schemaVars = schemaVars.append(schemaVar);
        }
        return schemaVars;
    }


    private OpReplacer createOpReplacer(ImmutableList<ProgramVariable> programVars,
            ImmutableList<SchemaVariable> schemaVars, TermServices services) {
        assert programVars.size() == schemaVars.size();
        final Map<ProgramVariable, ParsableVariable> map =
            new LinkedHashMap<>();
        Iterator<SchemaVariable> schemaIt = schemaVars.iterator();
        for (ProgramVariable progVar : programVars) {
            ParsableVariable schemaVar = schemaIt.next();
            if (progVar != null) {
                map.put(progVar, schemaVar);
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
    private TermAndBoundVarPair replaceBoundLogicVars(Term t, TermServices services) {
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
        for (Operator op : oc.ops()) {
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
        final Term newTerm = or.replace(intermediateRes.term);

        return new TermAndBoundVarPair(newTerm, newSVs);
    }


    private TermAndBoundVarPair replaceBoundLVsWithSVsHelper(Term t, TermServices services) {
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
        final Term[] newSubs = new Term[t.arity()];
        boolean changedSub = false;
        for (int i = 0; i < newSubs.length; i++) {
            if (t.op().bindVarsAt(i)) {
                newSubs[i] = or.replace(t.sub(i));
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
        final Term newTerm;
        if (map.isEmpty() && !changedSub) {
            newTerm = t;
        } else {
            newTerm = services.getTermBuilder().tf().createTerm(t.op(), newSubs,
                new ImmutableArray<>(newBoundVars), null);
        }

        return new TermAndBoundVarPair(newTerm, svs);
    }


    private Pair<Term, ImmutableSet<Taclet>> limitTerm(Term t,
            ImmutableSet<Pair<Sort, IObserverFunction>> toLimit, Services services) {
        ImmutableSet<Taclet> taclets = DefaultImmutableSet.nil();

        // recurse to subterms
        Term[] subs = new Term[t.arity()];
        for (int i = 0; i < subs.length; i++) {
            Pair<Term, ImmutableSet<Taclet>> pair = limitTerm(t.sub(i), toLimit, services);
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
        final Term term =
            services.getTermBuilder().tf().createTerm(newOp, subs, t.boundVars(), null);
        return new Pair<>(term, taclets);
    }


    private SequentFormula generateGuard(KeYJavaType kjt, IObserverFunction target,
            TermServices services, final SchemaVariable selfSV, List<SchemaVariable> heapSVs,
            ImmutableList<SchemaVariable> paramSVs, final Term schemaAxiom,
            final RewriteTacletBuilder<? extends RewriteTaclet> tacletBuilder, boolean addGuard) {
        final TermBuilder TB = services.getTermBuilder();
        final Term exactInstance = prepareExactInstanceGuard(kjt, target, services, selfSV);
        final Term axiomSatisfiable = addGuard
                ? prepareSatisfiabilityGuard(target, heapSVs, selfSV, paramSVs, schemaAxiom,
                    tacletBuilder, services)
                : TB.tt();
        // assemble formula
        final Term guardedAxiom = TB.imp(TB.and(exactInstance, axiomSatisfiable), schemaAxiom);
        final SequentFormula guardedAxiomCf = new SequentFormula(guardedAxiom);
        return guardedAxiomCf;
    }


    private Term prepareSatisfiabilityGuard(IObserverFunction target, List<SchemaVariable> heapSVs,
            final SchemaVariable selfSV, ImmutableList<SchemaVariable> paramSVs,
            final Term schemaAxiom,
            final RewriteTacletBuilder<? extends RewriteTaclet> tacletBuilder,
            TermServices services) {

        final TermBuilder TB = services.getTermBuilder();
        ImmutableList<Term> vars = ImmutableSLList.nil();
        for (SchemaVariable heapSV : heapSVs) {
            vars = vars.append(TB.var(heapSV));
        }
        if (!target.isStatic()) {
            vars = vars.append(TB.var(selfSV));
        }
        for (SchemaVariable sv : paramSVs) {
            vars = vars.append(TB.var(sv));
        }
        final Term targetTerm = TB.func(target, vars.toArray(new Term[0]));

        final Term axiomSatisfiable;
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
                tacletBuilder.addVarsNotFreeIn(targetSV, selfSV);
            }

            for (SchemaVariable paramSV : paramSVs) {
                tacletBuilder.addVarsNotFreeIn(targetSV, paramSV);
            }
            Term targetLVReachable = null;
            for (SchemaVariable heapSV : heapSVs) {
                final Term targetReachable =
                    TB.reachableValue(TB.var(heapSV), TB.var(targetSV), target.getType());
                if (targetLVReachable == null) {
                    targetLVReachable = targetReachable;
                } else {
                    targetLVReachable = TB.and(targetLVReachable, targetReachable);
                }
            }

            axiomSatisfiable =
                TB.ex(targetSV, TB.and(targetLVReachable, OpReplacer.replace(targetTerm,
                    TB.var(targetSV), schemaAxiom, services.getTermFactory())));
        }
        return axiomSatisfiable;
    }


    private Term prepareExactInstanceGuard(KeYJavaType kjt, IObserverFunction target,
            TermServices services, final SchemaVariable selfSV) {
        final boolean finalClass = kjt.getJavaType() instanceof ClassDeclaration
                && ((ClassDeclaration) kjt.getJavaType()).isFinal();
        // TODO: exact instance necessary?
        // or better: instance(finalClass, selfSV, services)?
        final TermBuilder TB = services.getTermBuilder();
        final Term exactInstance = target.isStatic() || finalClass ? TB.tt()
                : TB.exactInstance(kjt.getSort(), TB.var(selfSV));
        return exactInstance;
    }


    private record TermAndBoundVarPair(Term term, ImmutableSet<VariableSV> boundVars) {}
}
