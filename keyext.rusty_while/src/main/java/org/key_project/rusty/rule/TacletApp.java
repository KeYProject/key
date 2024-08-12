package org.key_project.rusty.rule;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;
import org.key_project.logic.Name;
import org.key_project.logic.Namespace;
import org.key_project.logic.Term;
import org.key_project.logic.op.Function;
import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.rusty.Services;
import org.key_project.rusty.logic.NamespaceSet;
import org.key_project.rusty.logic.PIOPathIterator;
import org.key_project.rusty.logic.PosInOccurrence;
import org.key_project.rusty.logic.op.LogicVariable;
import org.key_project.rusty.logic.op.sv.*;
import org.key_project.rusty.proof.Goal;
import org.key_project.rusty.rule.inst.InstantiationEntry;
import org.key_project.rusty.rule.inst.SVInstantiations;
import org.key_project.util.collection.*;

import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedHashMap;

public abstract class TacletApp implements RuleApp {
    /** the taclet for which the application information is collected */
    private final @NonNull Taclet taclet;

    /**
     * contains the instantiations of the schema variables of the Taclet
     */
    protected final SVInstantiations instantiations;

    /**
     * caches a created match condition {@code (instantiations, RenameTable.EMPTY)}
     */
    private final MatchConditions matchConditions;

    /**
     * chosen instantiations for the assumes-sequent formulas
     */
    protected final ImmutableList<IfFormulaInstantiation> ifInstantiations;

    /**
     * set of schema variables that appear in the Taclet and need to be instantiated but are not
     * instantiated yet. This means SchemaVariables in addrule-sections have to be ignored
     */
    private volatile ImmutableSet<SchemaVariable> missingVars = null;

    /**
     * the update context given by the current instantiations must not be changed
     */
    protected boolean updateContextFixed = false;

    /**
     * constructs a TacletApp for the given taclet, with an empty instantiation map
     */
    TacletApp(Taclet taclet) {
        this(taclet, SVInstantiations.EMPTY_SVINSTANTIATIONS, null);
    }

    TacletApp(Taclet taclet, SVInstantiations instantiations,
              ImmutableList<IfFormulaInstantiation> ifInstantiations) {
        this.taclet = taclet;
        this.instantiations = instantiations;
        this.ifInstantiations = ifInstantiations;
        this.matchConditions = new MatchConditions(instantiations);
    }

    /**
     * collects all bound variables above the occurrence of the schemavariable whose prefix is given
     *
     * @param prefix the TacletPrefix of the schemavariable
     * @param instantiations the SVInstantiations so that the find(if)-expression matches
     * @return set of the bound variables
     */
    protected static ImmutableSet<QuantifiableVariable> boundAtOccurrenceSet(TacletPrefix prefix,
                                                                             SVInstantiations instantiations) {
        return collectPrefixInstantiations(prefix, instantiations);
    }

    /**
     * collects all bound variables above the occurrence of the schemavariable whose prefix is given
     *
     * @param prefix the TacletPrefix of the schemavariable
     * @param instantiations the SVInstantiations so that the find(if)-expression matches
     * @param pos the posInOccurrence describing the position of the schemavariable
     * @return set of the bound variables
     */
    protected static ImmutableSet<QuantifiableVariable> boundAtOccurrenceSet(TacletPrefix prefix,
                                                                             SVInstantiations instantiations, PosInOccurrence pos) {

        ImmutableSet<QuantifiableVariable> result = boundAtOccurrenceSet(prefix, instantiations);

        if (prefix.context()) {
            result = result.union(collectBoundVarsAbove(pos));
        }

        return result;
    }

    /**
     * collects all those logic variable that are instances of the variableSV of the given prefix
     *
     * @param pre the TacletPrefix of a SchemaVariable that is bound
     * @param instantiations the SVInstantiations to look at
     * @return the set of the logic variables whose elements are the instantiations of a bound
     *         SchemaVariable appearing in the TacletPrefix
     */
    private static ImmutableSet<QuantifiableVariable> collectPrefixInstantiations(TacletPrefix pre,
                                                                                  SVInstantiations instantiations) {

        ImmutableSet<QuantifiableVariable> instanceSet =
                DefaultImmutableSet.nil();

        for (final SchemaVariable var : pre.prefix()) {
            instanceSet =
                    instanceSet.add((LogicVariable) ((Term) instantiations.getInstantiation(var)).op());
        }
        return instanceSet;
    }

    /**
     * returns the taclet the application information is collected for
     *
     * @return the Taclet the application information is collected for
     */
    public Taclet taclet() {
        return taclet;
    }

    /**
     * returns the rule the application information is collected for
     *
     * @return the Rule the application information is collected for
     */
    @Override
    public Taclet rule() {
        return taclet;
    }

    /**
     * returns the instantiations for the application of the Taclet at the specified position.
     *
     * @return the SVInstantiations needed to instantiate the Taclet
     */
    public SVInstantiations instantiations() {
        return instantiations;
    }

    public MatchConditions matchConditions() {
        return matchConditions;
    }

    public ImmutableList<IfFormulaInstantiation> ifFormulaInstantiations() {
        return ifInstantiations;
    }

    /**
     * creates a new Taclet application containing all the instantiations, constraints and new
     * metavariables given by the mc object and forget the old ones
     */
    public abstract TacletApp setMatchConditions(MatchConditions mc, Services services);

    /**
     * checks if the variable conditions of type 'x not free in y' are hold by the found
     * instantiations. The variable conditions is used implicit in the prefix. (Used to calculate
     * the prefix)
     *
     * @param taclet the Taclet that is tried to be instantiated. A match for the find (or/and if)
     *        has been found.
     * @param instantiations the SVInstantiations so that the find(if) expression matches
     * @param pos the PosInOccurrence where the Taclet is applied
     * @return true iff all variable conditions x not free in y are hold
     */
    public static boolean checkVarCondNotFreeIn(Taclet taclet, SVInstantiations instantiations,
                                                PosInOccurrence pos) {

        Iterator<SchemaVariable> it = instantiations.svIterator();
        while (it.hasNext()) {
            SchemaVariable sv = it.next();
            if (sv instanceof TermSV || sv instanceof FormulaSV) {
                if ( !((ImmutableSet<QuantifiableVariable>) ((Term) instantiations.getInstantiation(sv)).freeVars())
                        .subset(boundAtOccurrenceSet(taclet.getPrefix(sv), instantiations, pos))) {
                    return false;
                }
            }
        }
        return true;
    }

    /**
     * resolves collisions between bound SchemaVariables in an SVInstantiation
     *
     * @param insts the original SVInstantiations
     * @return the resolved SVInstantiations
     */
    protected static SVInstantiations resolveCollisionVarSV(Taclet taclet, SVInstantiations insts,
                                                            Services services) {

        HashMap<LogicVariable, SchemaVariable> collMap = new LinkedHashMap<>();

        final Iterator<ImmutableMapEntry<SchemaVariable, InstantiationEntry<?>>> it =
                insts.pairIterator();
        while (it.hasNext()) {
            ImmutableMapEntry<SchemaVariable, InstantiationEntry<?>> pair = it.next();
            if (pair.key() instanceof VariableSV) {
                SchemaVariable varSV = pair.key();
                Term value = (Term) pair.value().getInstantiation();
                if (!collMap.containsKey(value.op())) {
                    collMap.put((LogicVariable) value.op(), varSV);
                } else {
                    insts = replaceInstantiation(taclet, insts, varSV, services);
                }
            }
        }
        return insts;
    }

    /**
     * applies the specified rule at the specified position if all schema variables have been
     * instantiated
     *
     * @param goal the Goal at which the Taclet is applied
     * @param services the Services encapsulating all java information
     * @return list of new created goals
     */
    @Override
    public @Nullable ImmutableList<Goal> execute(Goal goal, Services services) {
        var time = System.nanoTime();
        try {
            var timePre = System.nanoTime();
            try {
                if (!complete()) {
                    throw new IllegalStateException(
                            "Tried to apply rule \n" + taclet + "\nthat is not complete." + this);
                }

                if (!isExecutable(services)) {
                    throw new RuntimeException(
                            "taclet application with unsatisfied 'checkPrefix': " + this);
                }
                registerSkolemConstants(goal.getLocalNamespaces());
                goal.addAppliedRuleApp(this);
            } finally {
                //PERF_PRE.getAndAdd(System.nanoTime() - timePre);
            }

            return taclet().apply(goal, services, this);
        } finally {
            //PERF_EXECUTE.getAndAdd(System.nanoTime() - time);
            //PERF_SET_SEQUENT.getAndAdd(Goal.PERF_SET_SEQUENT.get() - timeSetSequent);
        }
    }

    public boolean isExecutable(Services services) {
        // bugfix #1336, see bugtracker
        if (taclet instanceof RewriteTaclet rwt) {
            ImmutableList<Term> oldUpdCtx =
                    matchConditions().getInstantiations().getUpdateContext();
            MatchConditions newConditions = rwt.checkPrefix(posInOccurrence(),
                    MatchConditions.EMPTY_MATCHCONDITIONS);
            if (newConditions == null) {
                return false;
            }
            ImmutableList<Term> newUpdCtx =
                    newConditions.getInstantiations().getUpdateContext();
            return oldUpdCtx.equals(newUpdCtx);
        }
        return true;
    }

    /**
     * returns a new SVInstantiations that modifies the given SVInstantiations insts at the bound
     * SchemaVariable varSV to a new LogicVariable.
     */
    protected static SVInstantiations replaceInstantiation(Taclet taclet, SVInstantiations insts,
                                                           SchemaVariable varSV, Services services) {
        throw new RuntimeException("TODO");
        /*Term term = getTermBelowQuantifier(taclet, varSV);
        LogicVariable newVariable = new LogicVariable(
                new Name(((Term) insts.getInstantiation(varSV)).op().name() + "0"),
                ((Term) insts.getInstantiation(varSV)).sort());
        // __CHANGE__ How to name the new variable? TODO
        Term newVariableTerm = services.getTermBuilder().var(newVariable);
        return replaceInstantiation(insts, term, varSV, newVariableTerm, services);*/
    }

    /**
     * returns a new SVInstantiations that modifies the given SVInstantiations insts at the bound
     * SchemaVariable u to the Term (that is a LogicVariable) y.
     */
    private static SVInstantiations replaceInstantiation(SVInstantiations insts, Term t,
                                                         SchemaVariable u, Term y, Services services) {
        throw new RuntimeException("TODO");
/*
        SVInstantiations result = insts;
        LogicVariable x = (LogicVariable) ((Term) insts.getInstantiation(u)).op();
        if (t.op() instanceof SchemaVariable) {
            if (!(t.op() instanceof VariableSV)) {
                SchemaVariable sv = (SchemaVariable) t.op();
                ClashFreeSubst cfSubst = new ClashFreeSubst(x, y, services.getTermBuilder());
                result =
                        result.replace(sv, cfSubst.apply((Term) insts.getInstantiation(sv)), services);
            }
        } else {
            for (int i = 0; i < t.arity(); i++) {
                if (!contains(t.varsBoundHere(i), x, insts)) {
                    result = replaceInstantiation(result, t.sub(i), u, y, services);
                }
            }

        }

        result = result.replace(u, y, services);
        return result;*/
    }

    /**
     * delivers the term below the (unique) quantifier of a bound SchemaVariable in the given term.
     *
     * @param varSV the searched Bound Schemavariable
     * @param term the term to be searched in
     * @return the term below the given quantifier in the given term
     */
    private static Term getTermBelowQuantifier(SchemaVariable varSV, Term term) {
        for (int i = 0; i < term.arity(); i++) {
            for (int j = 0; j < term.varsBoundHere(i).size(); j++) {
                if (term.varsBoundHere(i).get(j) == varSV) {
                    return term.sub(i);
                }
            }
            Term rec = getTermBelowQuantifier(varSV, term.sub(i));
            if (rec != null) {
                return rec;
            }
        }
        return null;
    }

    /**
     * collects all bound vars that are bound above the subterm described by the given term position
     * information
     *
     * @param pos the PosInOccurrence describing a subterm in Term
     * @return a set of logic variables that are bound above the specified subterm
     */
    protected static ImmutableSet<QuantifiableVariable> collectBoundVarsAbove(PosInOccurrence pos) {
        ImmutableSet<QuantifiableVariable> result = DefaultImmutableSet.nil();

        PIOPathIterator it = pos.iterator();
        int i;
        ImmutableArray<? extends QuantifiableVariable> vars;

        while ((i = it.next()) != -1) {
            vars = it.getSubTerm().varsBoundHere(i);
            for (i = 0; i < vars.size(); i++) {
                result = result.add(vars.get(i));
            }
        }

        return result;
    }

    /**
     * calculate needed SchemaVariables that have not been instantiated yet. This means to ignore
     * SchemaVariables that appear only in addrule-sections of Taclets
     *
     * @return ImmutableSet<SchemaVariable> that need to be instantiated but are not
     */
    protected ImmutableSet<SchemaVariable> calculateNonInstantiatedSV() {
        if (missingVars == null) {
            ImmutableSet<SchemaVariable> localMissingVars =
                    DefaultImmutableSet.nil();
            TacletSchemaVariableCollector coll =
                    new TacletSchemaVariableCollector(instantiations());
            coll.visitWithoutAddrule(taclet());
            Iterator<SchemaVariable> it = coll.varIterator();
            while (it.hasNext()) {
                SchemaVariable var = it.next();
                if (!instantiations().isInstantiated(var)) {
                    localMissingVars = localMissingVars.add(var);
                }
            }
            missingVars = localMissingVars;
        }

        return missingVars;
    }

    /**
     * returns the variables that have not yet been instantiated and need to be instantiated to
     * apply the Taclet. (These are not all SchemaVariables like the one that appear only in the
     * addrule sections)
     *
     * @return ImmutableSet<SchemaVariable> with SchemaVariables that have not been instantiated yet
     */
    public ImmutableSet<SchemaVariable> uninstantiatedVars() {
        return calculateNonInstantiatedSV();
    }

    public void registerSkolemConstants(NamespaceSet nss) {
        final SVInstantiations insts = instantiations();
        final Iterator<SchemaVariable> svIt = insts.svIterator();
        while (svIt.hasNext()) {
            final SchemaVariable sv = svIt.next();
            if (sv instanceof SkolemTermSV) {
                final Term inst = (Term) insts.getInstantiation(sv);
                final Namespace<Function> functions = nss.functions();

                // skolem constant might already be registered in
                // case it is used in the \addrules() section of a rule
                if (functions.lookup(inst.op().name()) == null) {
                    functions.addSafely((Function) inst.op());
                }
            }
        }
    }

    /**
     * @return true iff the if-instantiation list is not null or no if sequent is needed
     */
    public boolean ifInstsComplete() {
        return ifInstantiations != null || taclet().ifSequent().isEmpty();
    }

    public PosTacletApp setPosInOccurrence(PosInOccurrence pos, Services services) {
        if (taclet() instanceof NoFindTaclet) {
            throw new IllegalStateException("Cannot add position to an taclet" + " without find");
        }
        return PosTacletApp.createPosTacletApp((FindTaclet) taclet(), instantiations(),
                ifFormulaInstantiations(), pos, services);
    }
}
