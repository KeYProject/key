package de.uka.ilkd.key.rule.executor.javadl;

import java.util.Collection;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.stream.Collectors;

import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.origin.OriginRef;
import de.uka.ilkd.key.logic.origin.OriginRefType;
import de.uka.ilkd.key.rule.*;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.label.TermLabelState;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.ProgVarReplacer;
import de.uka.ilkd.key.rule.Taclet.TacletLabelHint;
import de.uka.ilkd.key.rule.executor.RuleExecutor;
import de.uka.ilkd.key.rule.inst.GenericSortCondition;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.rule.tacletbuilder.TacletGoalTemplate;


/**
 * Encapsulates the application engine of taclets.
 *
 * @param <TacletKind> The kind of taclet that is executed.
 */
public abstract class TacletExecutor<TacletKind extends Taclet> implements RuleExecutor {

    private static final String AUTONAME = "_taclet";

    protected final TacletKind taclet;

    public TacletExecutor(TacletKind taclet) {
        this.taclet = taclet;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public abstract ImmutableList<Goal> apply(Goal goal, Services services, RuleApp tacletApp);


    /**
     * a new term is created by replacing variables of term whose replacement is found in the given
     * SVInstantiations
     *
     * @param term the {@link Term} the syntactical replacement is performed on
     * @param termLabelState The {@link TermLabelState} of the current rule application.
     * @param labelHint the hint used to maintain {@link TermLabel}s.
     * @param applicationPosInOccurrence the {@link PosInOccurrence} of the find term in the sequent
     *        this taclet is applied to
     * @param mc the {@link MatchConditions} with all instantiations and the constraint
     * @param goal the {@link Goal} on which this taclet is applied
     * @param ruleApp the {@link RuleApp} with application information
     * @param services the {@link Services} with the Java model information
     * @return the (partially) instantiated term
     */
    protected Term syntacticalReplace(Term term, TermLabelState termLabelState,
            TacletLabelHint labelHint, PosInOccurrence applicationPosInOccurrence,
            MatchConditions mc, Goal goal, RuleApp ruleApp, Services services) {
        final SyntacticalReplaceVisitor srVisitor =
            new SyntacticalReplaceVisitor(termLabelState, labelHint, applicationPosInOccurrence,
                mc.getInstantiations(), goal, taclet, ruleApp, services);
        term.execPostOrder(srVisitor);
        return srVisitor.getTerm();
    }

    /**
     * adds SequentFormula to antecedent or succedent depending on position information or the
     * boolean antec contrary to "addToPos" frm will not be modified
     *
     * @param frm the {@link SequentFormula} that should be added
     * @param currentSequent the {@link SequentChangeInfo} which is the current (intermediate)
     *        result of applying the taclet
     * @param pos the {@link PosInOccurrence} describing the place in the sequent
     * @param antec boolean true(false) if elements have to be added to the antecedent(succedent)
     *        (only looked at if pos == null)
     */
    private void addToPosWithoutInst(SequentFormula frm, SequentChangeInfo currentSequent,
            PosInOccurrence pos, boolean antec) {
        if (pos != null) {
            currentSequent.combine(currentSequent.sequent().addFormula(frm, pos));
        } else {
            // cf : formula to be added , 1. true/false: antec/succ,
            // 2. true: at head
            currentSequent.combine(currentSequent.sequent().addFormula(frm, antec, true));
        }
    }


    /**
     * the given constrained formula is instantiated and then the result (usually a complete
     * instantiated formula) is returned.
     *
     * @param termLabelState The {@link TermLabelState} of the current rule application.
     * @param schemaFormula the SequentFormula to be instantiated
     * @param services the Services object carrying ja related information
     * @param matchCond the MatchConditions object with the instantiations of the schemavariables,
     *        constraints etc.
     * @param applicationPosInOccurrence The {@link PosInOccurrence} of the {@link Term} which is
     *        rewritten
     * @param labelHint The hint used to maintain {@link TermLabel}s.
     * @return the as far as possible instantiated SequentFormula
     */
    private SequentFormula instantiateReplacement(TermLabelState termLabelState,
            SequentFormula schemaFormula, Services services, MatchConditions matchCond,
            PosInOccurrence applicationPosInOccurrence, TacletLabelHint labelHint, Goal goal,
            RuleApp tacletApp) {

        final SVInstantiations svInst = matchCond.getInstantiations();

        Term instantiatedFormula = syntacticalReplace(schemaFormula.formula(), termLabelState,
            new TacletLabelHint(labelHint, schemaFormula), applicationPosInOccurrence, matchCond,
            goal, tacletApp, services);

        if (!svInst.getUpdateContext().isEmpty()) {
            instantiatedFormula = services.getTermBuilder()
                    .applyUpdatePairsSequential(svInst.getUpdateContext(), instantiatedFormula);
        }

        if (applicationPosInOccurrence != null) {
            // if applicationPosInOccurence == null then the source term does not exist in the sequent (eg [CUT])

            Term apioTerm = applicationPosInOccurrence.subTerm();

            instantiatedFormula = updateOriginRefs(apioTerm, instantiatedFormula, services, goal, tacletApp);

        }

        return new SequentFormula(instantiatedFormula);
    }

    /**
     * instantiates the given semisequent with the instantiations found in Matchconditions
     *
     * @param semi the Semisequent to be instantiated
     * @param termLabelState The {@link TermLabelState} of the current rule application.
     * @param labelHint The hint used to maintain {@link TermLabel}s.
     * @param applicationPosInOccurrence The {@link PosInOccurrence} of the {@link Term} which is
     *        rewritten
     * @param matchCond the MatchConditions including the mapping Schemavariables to concrete logic
     *        elements
     * @param services the Services
     * @return the instantiated formulas of the semisequent as list
     */
    protected ImmutableList<SequentFormula> instantiateSemisequent(Semisequent semi,
            TermLabelState termLabelState, TacletLabelHint labelHint,
            PosInOccurrence applicationPosInOccurrence, MatchConditions matchCond, Goal goal,
            RuleApp tacletApp, Services services) {

        ImmutableList<SequentFormula> replacements = ImmutableSLList.<SequentFormula>nil();

        for (SequentFormula sf : semi) {
            replacements = replacements.append(instantiateReplacement(termLabelState, sf, services,
                matchCond, applicationPosInOccurrence, labelHint, goal, tacletApp));
        }

        return replacements;
    }



    /**
     * replaces the constrained formula at the given position with the first formula in the given
     * semisequent and adds possible other formulas of the semisequent starting at the position
     *
     * @param semi the Semisequent with the the ConstrainedFormulae to be added
     * @param termLabelState The {@link TermLabelState} of the current rule application.
     * @param currentSequent the Sequent which is the current (intermediate) result of applying the
     *        taclet
     * @param pos the PosInOccurrence describing the place in the sequent
     * @param matchCond the MatchConditions containing in particular
     * @param labelHint The hint used to maintain {@link TermLabel}s. the instantiations of the
     *        schemavariables
     * @param services the Services encapsulating all java information
     */
    protected void replaceAtPos(Semisequent semi, TermLabelState termLabelState,
            SequentChangeInfo currentSequent, PosInOccurrence pos, MatchConditions matchCond,
            TacletLabelHint labelHint, Goal goal, RuleApp ruleApp, Services services) {
        final ImmutableList<SequentFormula> replacements = instantiateSemisequent(semi,
            termLabelState, labelHint, pos, matchCond, goal, ruleApp, services);
        currentSequent.combine(currentSequent.sequent().changeFormula(replacements, pos));
    }

    /**
     * instantiates the constrained formulas of semisequent <code>semi</code> and adds the
     * instantiatied formulas at the specified position to <code>goal</code>
     *
     * @param semi the Semisequent with the the ConstrainedFormulae to be added
     * @param termLabelState The {@link TermLabelState} of the current rule application.
     * @param currentSequent the Sequent which is the current (intermediate) result of applying the
     *        taclet
     * @param pos the PosInOccurrence describing the place in the sequent
     * @param applicationPosInOccurrence The {@link PosInOccurrence} of the {@link Term} which is
     *        rewritten
     * @param antec boolean true(false) if elements have to be added to the antecedent(succedent)
     *        (only looked at if pos == null)
     * @param labelHint The hint used to maintain {@link TermLabel}s. the instantiations of the
     *        schemavariables
     * @param matchCond the MatchConditions containing in particular
     * @param services the Services encapsulating all java information
     */
    private void addToPos(Semisequent semi, TermLabelState termLabelState,
            SequentChangeInfo currentSequent, PosInOccurrence pos,
            PosInOccurrence applicationPosInOccurrence, boolean antec, TacletLabelHint labelHint,
            MatchConditions matchCond, Goal goal, Services services, RuleApp tacletApp) {

        final ImmutableList<SequentFormula> replacements =
            instantiateSemisequent(semi, termLabelState, labelHint, applicationPosInOccurrence,
                matchCond, goal, tacletApp, services);
        if (pos != null) {
            currentSequent.combine(currentSequent.sequent().addFormula(replacements, pos));
        } else {
            currentSequent.combine(currentSequent.sequent().addFormula(replacements, antec, true));
        }
    }

    /**
     * adds SequentFormula to antecedent depending on position information (if none is handed over
     * it is added at the head of the antecedent). Of course it has to be ensured that the position
     * information describes one occurrence in the antecedent of the sequent.
     *
     * @param semi the Semisequent with the the ConstrainedFormulae to be added
     * @param termLabelState The {@link TermLabelState} of the current rule application.
     * @param labelHint The hint used to maintain {@link TermLabel}s.
     * @param currentSequent the Sequent which is the current (intermediate) result of applying the
     *        taclet
     * @param pos the PosInOccurrence describing the place in the sequent or null for head of
     *        antecedent
     * @param applicationPosInOccurrence The {@link PosInOccurrence} of the {@link Term} which is
     *        rewritten
     * @param matchCond the MatchConditions containing in particular the instantiations of the
     *        schemavariables
     * @param services the Services encapsulating all java information
     */
    protected void addToAntec(Semisequent semi, TermLabelState termLabelState,
            TacletLabelHint labelHint, SequentChangeInfo currentSequent, PosInOccurrence pos,
            PosInOccurrence applicationPosInOccurrence, MatchConditions matchCond, Goal goal,
            RuleApp tacletApp, Services services) {
        addToPos(semi, termLabelState, currentSequent, pos, applicationPosInOccurrence, true,
            labelHint, matchCond, goal, services, tacletApp);
    }

    /**
     * adds SequentFormula to succedent depending on position information (if none is handed over it
     * is added at the head of the succedent). Of course it has to be ensured that the position
     * information describes one occurrence in the succedent of the sequent.
     *
     * @param semi the Semisequent with the the ConstrainedFormulae to be added
     * @param termLabelState The {@link TermLabelState} of the current rule application.
     * @param labelHint The hint used to maintain {@link TermLabel}s.
     * @param pos the PosInOccurrence describing the place in the sequent or null for head of
     *        antecedent
     * @param applicationPosInOccurrence The {@link PosInOccurrence} of the {@link Term} which is
     *        rewritten
     * @param matchCond the MatchConditions containing in particular the instantiations of the
     *        schemavariables
     * @param goal the Goal that knows the node the formulae have to be added
     * @param services the Services encapsulating all java information
     */
    protected void addToSucc(Semisequent semi, TermLabelState termLabelState,
            TacletLabelHint labelHint, SequentChangeInfo currentSequent, PosInOccurrence pos,
            PosInOccurrence applicationPosInOccurrence, MatchConditions matchCond, Goal goal,
            RuleApp ruleApp, Services services) {
        addToPos(semi, termLabelState, currentSequent, pos, applicationPosInOccurrence, false,
            labelHint, matchCond, goal, services, ruleApp);
    }


    /**
     * adds the given rules (i.e. the rules to add according to the Taclet goal template to the node
     * of the given goal
     *
     * @param rules the rules to be added
     * @param goal the goal describing the node where the rules should be added
     * @param services the Services encapsulating all java information
     * @param matchCond the MatchConditions containing in particular the instantiations of the
     *        schemavariables
     */
    protected void applyAddrule(ImmutableList<Taclet> rules, Goal goal, Services services,
            MatchConditions matchCond) {

        for (Taclet tacletToAdd : rules) {
            final Node n = goal.node();
            final StringBuilder uniqueTail = new StringBuilder(tacletToAdd.name().toString());
            uniqueTail.append(AUTONAME).append(n.getUniqueTacletId());
            tacletToAdd = tacletToAdd.setName(uniqueTail.toString());


            // the new Taclet may contain variables with a known
            // instantiation. These must be used by the new Taclet and all
            // further rules it contains in the addrules-sections. Therefore all
            // appearing (including the addrules) SchemaVariables have to be
            // collected, then it is looked if an instantiation is known and if
            // positive the instantiation is memorized. At last the Taclet with
            // its required instantiations is handed over to the goal, where a
            // new TacletApp should be built including the necessary instantiation
            // information

            SVInstantiations neededInstances = SVInstantiations.EMPTY_SVINSTANTIATIONS
                    .addUpdateList(matchCond.getInstantiations().getUpdateContext());

            final TacletSchemaVariableCollector collector = new TacletSchemaVariableCollector();
            collector.visit(tacletToAdd, true);// true, because
            // descend into addrules
            for (SchemaVariable sv : collector.vars()) {
                if (matchCond.getInstantiations().isInstantiated(sv)) {
                    neededInstances = neededInstances.add(sv,
                        matchCond.getInstantiations().getInstantiationEntry(sv), services);
                }
            }

            final ImmutableList<GenericSortCondition> cs =
                matchCond.getInstantiations().getGenericSortInstantiations().toConditions();

            for (final GenericSortCondition gsc : cs) {
                neededInstances = neededInstances.add(gsc, services);
            }

            goal.addTaclet(tacletToAdd, neededInstances, true);
        }
    }


    protected void applyAddProgVars(ImmutableSet<SchemaVariable> pvs,
            SequentChangeInfo currentSequent, Goal goal, PosInOccurrence posOfFind,
            Services services, MatchConditions matchCond) {
        ImmutableList<RenamingTable> renamings = ImmutableSLList.<RenamingTable>nil();
        for (final SchemaVariable sv : pvs) {
            final ProgramVariable inst =
                (ProgramVariable) matchCond.getInstantiations().getInstantiation(sv);
            // if the goal already contains the variable to be added
            // (not just a variable with the same name), then there is nothing to do
            Collection<IProgramVariable> progVars =
                goal.getLocalNamespaces().programVariables().elements();
            if (progVars.contains(inst)) {
                continue;
            }

            final VariableNamer vn = services.getVariableNamer();
            final ProgramVariable renamedInst = vn.rename(inst, goal, posOfFind);
            goal.addProgramVariable(renamedInst);
            services.addNameProposal(renamedInst.name());

            HashMap<ProgramVariable, ProgramVariable> renamingMap = vn.getRenamingMap();
            if (!renamingMap.isEmpty()) {
                // execute renaming
                final ProgVarReplacer pvr = new ProgVarReplacer(vn.getRenamingMap(), services);

                // globals
                // we do not need to do the old assignment
                // goal.setGlobalProgVars(pvr.replace(Immutables.createSetFrom(progVars)));
                // as the following assertions ensure it would have no effect anyways.
                assert renamingMap.size() == 1;
                assert renamingMap.get(inst) == renamedInst;
                assert !progVars.contains(inst);

                // taclet apps
                pvr.replace(goal.ruleAppIndex().tacletIndex());

                // sequent
                currentSequent.combine(pvr.replace(currentSequent.sequent()));

                final RenamingTable rt = RenamingTable.getRenamingTable(vn.getRenamingMap());

                renamings = renamings.append(rt);
            }
        }
        goal.node().setRenamings(renamings);
    }


    /**
     * Search for formulas within p_list that have to be proved by an explicit assumes-goal, i.e.
     * elements of type IfFormulaInstDirect.
     *
     * @param p_goal the {@link Goal} on which the taclet is applied
     * @param p_list the list of {@link IfFormulaInstantiation} containing the instantiations for
     *        the assumes formulas
     * @param p_matchCond the {@link MatchConditions} with the instantiations of the schema
     *        variables
     * @param p_numberOfNewGoals the number of new goals the {@link Taclet} creates in any case
     *        because of existing {@link TacletGoalTemplate}s
     * @return a list with the original sequent if no such formulas existed, otherwise the list has
     *         two entries: one for the original sequent and one with the sequent encoding the proof
     *         obligation for the to be proven formulas of the assumes goal
     */
    protected ImmutableList<SequentChangeInfo> checkIfGoals(Goal p_goal,
            ImmutableList<IfFormulaInstantiation> p_list, MatchConditions p_matchCond,
            int p_numberOfNewGoals) {
        ImmutableList<SequentChangeInfo> res = null;
        Iterator<SequentChangeInfo> itNewGoalSequents;

        // proof obligation for the if formulas
        Term ifObl = null;

        // always create at least one new goal
        if (p_numberOfNewGoals == 0)
            p_numberOfNewGoals = 1;

        if (p_list != null) {
            int i = taclet.ifSequent().antecedent().size();
            Term ifPart;

            for (final IfFormulaInstantiation inst : p_list) {
                if (!(inst instanceof IfFormulaInstSeq)) {
                    // build the if obligation formula
                    ifPart = inst.getConstrainedFormula().formula();

                    // negate formulas of the if succedent
                    final TermServices services = p_goal.proof().getServices();
                    if (i <= 0)
                        ifPart = services.getTermBuilder().not(ifPart);

                    if (res == null) {
                        res = ImmutableSLList.<SequentChangeInfo>nil();
                        for (int j = 0; j < p_numberOfNewGoals + 1; j++) {
                            res = res.prepend(SequentChangeInfo.createSequentChangeInfo(
                                (SemisequentChangeInfo) null, (SemisequentChangeInfo) null,
                                p_goal.sequent(), p_goal.sequent()));
                        }
                        ifObl = ifPart;
                    } else {
                        ifObl = services.getTermFactory().createTerm(Junctor.AND, ifObl, ifPart);
                    }

                    // UGLY: We create a flat structure of the new
                    // goals, thus the if formulas have to be added to
                    // every new goal
                    itNewGoalSequents = res.iterator();
                    SequentChangeInfo seq = itNewGoalSequents.next();
                    while (itNewGoalSequents.hasNext()) {
                        // (i > 0) iff inst is formula of the antecedent
                        addToPosWithoutInst(inst.getConstrainedFormula(), seq, null, (i > 0));
                        seq = itNewGoalSequents.next();
                    }
                }

                --i;
            }
        }

        if (res == null) {
            res = ImmutableSLList.<SequentChangeInfo>nil();
            for (int j = 0; j < p_numberOfNewGoals; j++) {
                res = res.prepend(
                    SequentChangeInfo.createSequentChangeInfo((SemisequentChangeInfo) null,
                        (SemisequentChangeInfo) null, p_goal.sequent(), p_goal.sequent()));
            }
        } else {
            // find the sequent the if obligation has to be added to
            itNewGoalSequents = res.iterator();
            SequentChangeInfo seq = itNewGoalSequents.next();
            while (itNewGoalSequents.hasNext()) {
                seq = itNewGoalSequents.next();
            }

            addToPosWithoutInst(new SequentFormula(ifObl), seq, null, false);
        }

        return res;
    }

    protected Term updateOriginRefs(Term findTerm, Term replTerm, Services svc, Goal goal, RuleApp ruleApp) {
        TermFactory tf = svc.getTermFactory();

        // remove UNKNOWN|no-src origins ( can come from invariant instanciations )
        if (replTerm.getOriginRef().stream().anyMatch(p -> p.Type == OriginRefType.UNKNOWN && !p.hasFile())) {
            List<OriginRef> cleaned = replTerm.getOriginRef().stream().filter(p -> p.Type != OriginRefType.UNKNOWN || p.hasFile()).collect(Collectors.toList());
            replTerm = tf.setOriginRef(replTerm, cleaned);
        }

        if (replTerm.getOriginRef().isEmpty()) {
            // do not add a new origin if the term already has one
            // this means that we haven't created a new term but extracted a sub-term from the find clause
            // (e.g. andLeft{} )
            // in this case we do _not_ wand to add the find origin to the origin-list
            replTerm = tf.addOriginRef(replTerm, findTerm.getOriginRef());
        }

        if (ruleApp instanceof TacletApp) {
            var ifinst = ((TacletApp)ruleApp).ifFormulaInstantiations();
            if (ifinst != null) {
                var assumeTerms = ifinst.stream().map(p -> p.getConstrainedFormula().formula()).collect(Collectors.toList());
                for (Term at: assumeTerms) {
                    replTerm = tf.addOriginRef(replTerm, at.getOriginRef());
                }
            }
        }

        SourceElement procStmt = getProcessedStatement(goal, findTerm, replTerm);
        if (procStmt != null) {
            // We land here if:
            // - The taclet matched a diamond-op replTerm java code
            // - And replaced it replTerm an update-application
            // - and we found a node with an activeStatement replTerm a valid PositionInfo
            // --> TODO check this logic

            OriginRef origref = OriginRef.fromStatement(procStmt);

            replTerm = patchCreatedUpdateApplicationOrigin(tf, replTerm, origref);
        }

        return replTerm;
    }

    private Term patchCreatedUpdateApplicationOrigin(TermFactory tf, Term t, OriginRef origref) {
        Term s1 = t.sub(0);
        Term s2 = t.sub(1);

        if (s2.op() != UpdateApplication.UPDATE_APPLICATION) {
            s1 = tf.addOriginRefRecursive(s1, origref);
            return tf.createTerm(t.op(), new ImmutableArray<>(s1, s2), t.boundVars(), t.javaBlock(), t.getLabels(), t.getOriginRef());
        } else {
            s2 = patchCreatedUpdateApplicationOrigin(tf, s2, origref);
            return tf.createTerm(t.op(), new ImmutableArray<>(s1, s2), t.boundVars(), t.javaBlock(), t.getLabels(), t.getOriginRef());
        }
    }

    private Term getCreatedUpdateApplicationOrigin(Term t) {
        if (t.op() != UpdateApplication.UPDATE_APPLICATION) {
            return null;
        }

        Term s1 = t.sub(0);
        Term s2 = t.sub(1);

        if (s2.op() != UpdateApplication.UPDATE_APPLICATION) {
            return s1;
        } else {
            return getCreatedUpdateApplicationOrigin(s2);
        }
    }

    private SourceElement getProcessedStatement(Goal goal, Term findTerm, Term replTerm) {

        while (findTerm.op() instanceof UpdateApplication) {
            findTerm = findTerm.sub(1);
        }

        if (findTerm.javaBlock() == null) return null;
        if (findTerm.op() != Modality.DIA) return null;

        Term newUpdate = getCreatedUpdateApplicationOrigin(replTerm);
        if (newUpdate == null) return null;

        if (replTerm.op() != UpdateApplication.UPDATE_APPLICATION) return null;
        if (!newUpdate.getOriginRefRecursive().isEmpty()) return null;

        Node node = goal.node();
        SourceElement activeStatement = null;
        while ((activeStatement == null || activeStatement.getPositionInfo() == PositionInfo.UNDEFINED || activeStatement.getPositionInfo().getURI() == PositionInfo.UNKNOWN_URI) && node != null) {
            activeStatement = node.getNodeInfo().getActiveStatement();
            node = node.parent();
        }

        if (activeStatement == null) return null;

        if (activeStatement.getPositionInfo() == PositionInfo.UNDEFINED) return null;
        if (activeStatement.getPositionInfo().getURI() == PositionInfo.UNKNOWN_URI) return null;

        return activeStatement;
    }
}
