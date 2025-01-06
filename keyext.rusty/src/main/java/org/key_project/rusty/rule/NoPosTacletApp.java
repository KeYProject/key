/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.rule;


import org.key_project.logic.Term;
import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.prover.rules.AssumesFormulaInstantiation;
import org.key_project.prover.rules.MatchConditions;
import org.key_project.prover.rules.inst.SVInstantiations;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.rusty.Services;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSet;

public class NoPosTacletApp extends TacletApp {
    /**
     * creates a NoPosTacletApp for the given taclet and no instantiation information and CHECKS
     * variable conditions as well as it resolves collisions
     *
     * @param taclet the Taclet
     */
    public static NoPosTacletApp createNoPosTacletApp(Taclet taclet) {
        return new UninstantiatedNoPosTacletApp(taclet);
    }

    /**
     * creates a NoPosTacletApp for the given taclet with some known instantiations and CHECKS
     * variable conditions as well as it resolves collisions The ifInstantiations parameter is not
     * matched against the if sequence, but only stored. For matching use the method
     * "setIfFormulaInstantiations".
     *
     * @param taclet the Taclet
     * @param instantiations the SVInstantiations
     */
    public static NoPosTacletApp createNoPosTacletApp(Taclet taclet,
            SVInstantiations instantiations, Services services) {
        return createNoPosTacletApp(taclet, instantiations, null, services);
    }

    public static NoPosTacletApp createNoPosTacletApp(Taclet taclet,
            SVInstantiations instantiations,
            ImmutableList<AssumesFormulaInstantiation> ifInstantiations,
            Services services) {
        SVInstantiations inst = resolveCollisionVarSV(taclet, instantiations, services);
        if (checkNoFreeVars(taclet)) {
            return new NoPosTacletApp(taclet, inst, ifInstantiations);
        }
        return null;
    }

    public static NoPosTacletApp createNoPosTacletApp(Taclet taclet, MatchConditions matchCond,
            Services services) {
        return createNoPosTacletApp(taclet, matchCond.getInstantiations(), null, services);
    }

    /**
     * Create TacletApp with immutable "instantiations", i.e. this instantiations must not be
     * modified later (e.g. by "addInstantiation"). However, this information is currently only used
     * to decide about introduction of metavariables. Immutable instantiations are important for the
     * "addrules" part of taclets.
     */
    public static NoPosTacletApp createFixedNoPosTacletApp(Taclet taclet,
            SVInstantiations instantiations, Services services) {
        NoPosTacletApp res = createNoPosTacletApp(taclet, instantiations, null, services);
        // Make the given SVs fixed
        if (res != null) {
            res.updateContextFixed = true;
        }
        return res;
    }


    /**
     * creates a NoPosTacletApp for the given taclet and no instantiation information
     *
     * @param taclet the Taclet
     */
    protected NoPosTacletApp(Taclet taclet) {
        super(taclet);
    }

    /**
     * creates a NoPosTacletApp for the given taclet with some known instantiations
     *
     * @param taclet the Taclet
     * @param instantiations the SVInstantiations
     */
    private NoPosTacletApp(Taclet taclet, SVInstantiations instantiations,
            ImmutableList<AssumesFormulaInstantiation> ifInstantiations) {
        super(taclet, instantiations, ifInstantiations);
    }

    protected MatchConditions setupMatchConditions(PosInOccurrence pos, Services services) {
        var svInst =
            (org.key_project.rusty.rule.inst.SVInstantiations) (taclet() instanceof NoFindTaclet
                    ? instantiations()
                    : instantiations().clearUpdateContext());

        org.key_project.rusty.rule.MatchConditions mc;
        if (svInst.isEmpty()) {
            mc = org.key_project.rusty.rule.MatchConditions.EMPTY_MATCHCONDITIONS;
        } else {
            mc = new org.key_project.rusty.rule.MatchConditions(svInst);
        }

        if (taclet() instanceof RewriteTaclet) {
            mc = ((RewriteTaclet) taclet()).checkPrefix(pos, mc);
        }

        return mc;
    }

    /**
     * returns the PositionInOccurrence (representing a SequentFormula and a position in the
     * corresponding formula)
     *
     * @return the PosInOccurrence
     */
    @Override
    public PosInOccurrence posInOccurrence() {
        return null;
    }

    /**
     * returns true iff all necessary informations are collected, so that the Taclet can be applied.
     *
     * @return true iff all necessary informations are collected, so that the Taclet can be applied.
     */
    @Override
    public boolean complete() {
        return (uninstantiatedVars().isEmpty() && taclet() instanceof NoFindTaclet
                && ifInstsComplete());

    }

    /**
     * PRECONDITION:
     *
     * <pre>
     *  {@code
     * ifFormulaInstantiations () == null &&
     *   ( pos == null || termConstraint.isSatisfiable () )
     * }
     * </pre>
     *
     * @return TacletApp with the resulting instantiations or null
     */
    public NoPosTacletApp matchFind(PosInOccurrence pos, Services services) {
        return matchFind(pos, services, null);
    }

    public NoPosTacletApp matchFind(PosInOccurrence pos, Services services, Term t) {
        if ((t == null) && (pos != null)) {
            t = pos.subTerm();
        }

        MatchConditions mc = setupMatchConditions(pos, services);
        if (mc == null) {
            return null;
        }

        MatchConditions res;
        if (taclet() instanceof FindTaclet) {
            res = taclet().getMatcher().matchFind(t, mc, services);
            // the following check will partly be repeated within the
            // constructor; this could be optimised
            if (res == null || !checkVarCondNotFreeIn(taclet(), res.getInstantiations(), pos)) {
                return null;
            }
        } else {
            res = mc;
        }
        return evalCheckRes(res, services);
    }

    private NoPosTacletApp evalCheckRes(MatchConditions res, Services services) {
        if (res == null) {
            return null;
        }

        if (updateContextFixed
                && !updateContextCompatible((org.key_project.rusty.rule.MatchConditions) res)) {
            /*
             * LOGGER.debug("NoPosTacletApp: Incompatible context", instantiations.getUpdateContext
             * (), res.matchConditions().getInstantiations().getUpdateContext());
             */
            return null;
        }

        return (NoPosTacletApp) setMatchConditions(res, services);
    }

    /**
     * creates a new Taclet application containing all the instantiations, constraints and new
     * metavariables given by the mc object and forget the old ones
     */
    @Override
    public TacletApp setMatchConditions(MatchConditions mc, Services services) {
        return createNoPosTacletApp(taclet(), mc.getInstantiations(),
            assumesFormulaInstantiations(),
            services);
    }

    /**
     * creates a new Taclet application containing all the instantiations, constraints, new
     * metavariables and if formula instantiations given and forget the old ones
     */
    @Override
    protected TacletApp setAllInstantiations(MatchConditions mc,
            ImmutableList<AssumesFormulaInstantiation> ifInstantiations, Services services) {
        return createNoPosTacletApp(taclet(), mc.getInstantiations(), ifInstantiations, services);
    }

    private boolean updateContextCompatible(org.key_project.rusty.rule.MatchConditions p_mc) {
        return instantiations.getUpdateContext()
                .equals(p_mc.getInstantiations().getUpdateContext());
    }

    /**
     * adds a new instantiation to this TacletApp
     *
     * @param sv the SchemaVariable to be instantiated
     * @param term the Term the SchemaVariable is instantiated with
     * @return the new TacletApp
     */
    @Override
    public TacletApp addInstantiation(SchemaVariable sv, Term term, boolean interesting,
            Services services) {
        /*
         * if (interesting) {
         * return createNoPosTacletApp(taclet(),
         * instantiations().addInteresting(sv, term, services), ifFormulaInstantiations(),
         * services);
         * } else
         */ {
            return createNoPosTacletApp(taclet(), instantiations().add(sv, term, services),
                assumesFormulaInstantiations(), services);
        }
    }

    @Override
    public String toString() {
        return super.toString() + " at " + posInOccurrence();
    }

    @Override
    protected ImmutableSet<QuantifiableVariable> contextVars(SchemaVariable sv) {
        return DefaultImmutableSet.nil();
    }

    @Override
    public TacletApp addInstantiation(SVInstantiations svi, Services services) {
        return new NoPosTacletApp(taclet(), svi.union(instantiations(), services),
            assumesFormulaInstantiations());
    }
}
