/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule;

import java.util.Iterator;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.RenameTable;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.util.Debug;

import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSet;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * A no position taclet application has no position information yet. This can have different
 * reasons:
 * <ul>
 * <li>the taclet application belongs to a no find taclet, this means it is attached to a sequent
 * and not to a formula or term.</li>
 * <li>the taclet application has not been matched against a term or formula, but may already
 * contain instantiation information for some of its schemavariables. This is the case, if the
 * taclet of this application object has been inserted by an addrule part of another taclet. For
 * this reason the {@link de.uka.ilkd.key.proof.TacletIndex} manages no position taclet application
 * objects instead of the taclets itself.</li>
 * </ul>
 *
 */
public class NoPosTacletApp extends TacletApp {
    public static final Logger LOGGER = LoggerFactory.getLogger(NoPosTacletApp.class);

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
            SVInstantiations instantiations, ImmutableList<IfFormulaInstantiation> ifInstantiations,
            Services services) {
        Debug.assertTrue(ifInstsCorrectSize(taclet, ifInstantiations),
            "If instantiations list has wrong size");

        SVInstantiations inst = resolveCollisionVarSV(taclet, instantiations, services);
        if (checkVarCondNotFreeIn(taclet, inst)) {
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
            ImmutableList<IfFormulaInstantiation> ifInstantiations) {
        super(taclet, instantiations, ifInstantiations);
    }


    /**
     * checks if the variable conditions of type 'x not free in y' are hold by the found
     * instantiations. The variable conditions is used implicit in the prefix. (Used to calculate
     * the prefix)
     *
     * @param taclet the Taclet that is tried to be instantiated. A match for the find (or/and if)
     *        has been found.
     * @param instantiations the SVInstantiations so that the find(if) matches
     * @return true iff all variable conditions x not free in y are hold
     */
    protected static boolean checkVarCondNotFreeIn(Taclet taclet, SVInstantiations instantiations) {
        final Iterator<SchemaVariable> it = instantiations.svIterator();
        while (it.hasNext()) {
            final SchemaVariable sv = it.next();

            if (sv instanceof ModalOperatorSV || sv instanceof ProgramSV || sv instanceof VariableSV
                    || sv instanceof SkolemTermSV) {
                continue;
            }

            final TacletPrefix prefix = taclet.getPrefix(sv);
            if (prefix.context()) {
                continue;
            }

            final ImmutableSet<QuantifiableVariable> boundVarSet =
                boundAtOccurrenceSet(prefix, instantiations);
            final Term inst = (Term) instantiations.getInstantiation(sv);
            if (!inst.freeVars().subset(boundVarSet)) {
                return false;
            }
        }

        return true;
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
        if (interesting) {
            return createNoPosTacletApp(taclet(),
                instantiations().addInteresting(sv, term, services), ifFormulaInstantiations(),
                services);
        } else {
            return createNoPosTacletApp(taclet(), instantiations().add(sv, term, services),
                ifFormulaInstantiations(), services);
        }
    }



    @Override
    public TacletApp addInstantiation(SchemaVariable sv, Object[] list, boolean interesting,
            Services services) {
        if (interesting) {
            return createNoPosTacletApp(taclet(),
                instantiations().addInterestingList(sv, list, services), ifFormulaInstantiations(),
                services);
        } else {
            return createNoPosTacletApp(taclet(), instantiations().addList(sv, list, services),
                ifFormulaInstantiations(), services);
        }
    }



    /**
     * adds a new instantiation to this TacletApp
     *
     * @param sv the SchemaVariable to be instantiated
     * @param pe the ProgramElement the SV is instantiated with
     * @return the new TacletApp
     */
    @Override
    public TacletApp addInstantiation(SchemaVariable sv, ProgramElement pe, boolean interesting,
            Services services) {
        if (interesting) {
            return createNoPosTacletApp(taclet(), instantiations().addInteresting(sv, pe, services),
                ifFormulaInstantiations(), services);
        } else {
            return createNoPosTacletApp(taclet(), instantiations().add(sv, pe, services),
                ifFormulaInstantiations(), services);
        }
    }


    /**
     * creates a new Taclet application containing all the instantiations given by the
     * SVInstantiations and hold the old ones
     *
     * @param svi the SVInstantiations whose entries are the needed instantiations
     * @return the new Taclet application
     */
    @Override
    public TacletApp addInstantiation(SVInstantiations svi, Services services) {
        return new NoPosTacletApp(taclet(), svi.union(instantiations(), services),
            ifFormulaInstantiations());
    }


    /**
     * creates a new Taclet application containing all the instantiations given by the
     * SVInstantiations and forget the ones in this TacletApp
     *
     * @param svi the SVInstantiations whose entries are the needed instantiations
     * @return the new Taclet application
     */
    @Override
    protected TacletApp setInstantiation(SVInstantiations svi, Services services) {
        return new NoPosTacletApp(taclet(), svi, ifFormulaInstantiations());
    }


    /**
     * creates a new Taclet application containing all the instantiations, constraints and new
     * metavariables given by the mc object and forget the old ones
     */
    @Override
    public TacletApp setMatchConditions(MatchConditions mc, Services services) {
        return createNoPosTacletApp(taclet(), mc.getInstantiations(), ifFormulaInstantiations(),
            services);
    }


    /**
     * creates a new Taclet application containing all the instantiations, constraints, new
     * metavariables and if formula instantiations given and forget the old ones
     */
    @Override
    protected TacletApp setAllInstantiations(MatchConditions mc,
            ImmutableList<IfFormulaInstantiation> ifInstantiations, Services services) {
        return createNoPosTacletApp(taclet(), mc.getInstantiations(), ifInstantiations, services);
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

    @Override
    protected ImmutableSet<QuantifiableVariable> contextVars(SchemaVariable sv) {
        return DefaultImmutableSet.nil();
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
     * PRECONDITION: ifFormulaInstantiations () == null && ( pos == null ||
     * termConstraint.isSatisfiable () )
     *
     * @return TacletApp with the resulting instantiations or null
     */
    public NoPosTacletApp matchFind(PosInOccurrence pos, Services services) {
        NoPosTacletApp result = matchFind(pos, services, null);
        return result;
    }


    /*
     * This is a short-circuit version of matchFind(). It helps eliminate numerous calls to the
     * expensive pos.subTerm() while matching during a recursive descent in a term (where the
     * current subterm is known anyway).
     */
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

        if (updateContextFixed && !updateContextCompatible(res)) {
            /*
             * LOGGER.debug("NoPosTacletApp: Incompatible context", instantiations.getUpdateContext
             * (), res.matchConditions().getInstantiations().getUpdateContext());
             */
            return null;
        }

        return (NoPosTacletApp) setMatchConditions(res, services);
    }


    protected MatchConditions setupMatchConditions(PosInOccurrence pos, TermServices services) {
        SVInstantiations svInst = taclet() instanceof NoFindTaclet ? instantiations()
                : instantiations().clearUpdateContext();

        MatchConditions mc;
        if (svInst.isEmpty()) {
            mc = MatchConditions.EMPTY_MATCHCONDITIONS;
        } else {
            mc = new MatchConditions(svInst, RenameTable.EMPTY_TABLE);
        }

        if (taclet() instanceof RewriteTaclet) {
            mc = ((RewriteTaclet) taclet()).checkPrefix(pos, mc);
        }

        return mc;
    }


    private boolean updateContextCompatible(MatchConditions p_mc) {
        return instantiations.getUpdateContext()
                .equals(p_mc.getInstantiations().getUpdateContext());
    }
}
