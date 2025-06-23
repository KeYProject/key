/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule;


import java.util.Collections;
import java.util.Set;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.RenameTable;
import de.uka.ilkd.key.util.Debug;

import org.key_project.logic.LogicServices;
import org.key_project.logic.SyntaxElement;
import org.key_project.logic.Term;
import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.prover.rules.instantiation.AssumesFormulaInstantiation;
import org.key_project.prover.rules.instantiation.MatchResultInfo;
import org.key_project.prover.rules.instantiation.SVInstantiations;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.util.collection.ImmutableList;

import org.jspecify.annotations.Nullable;
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
     * matched against the assumes-sequence, but only stored. For matching use the method
     * "setIfFormulaInstantiations".
     *
     * @param taclet the Taclet
     * @param instantiations the SVInstantiations
     */
    public static NoPosTacletApp createNoPosTacletApp(Taclet taclet,
            SVInstantiations instantiations, Services services) {
        return createNoPosTacletApp(taclet, instantiations, null, services);
    }

    public static NoPosTacletApp createNoPosTacletApp(org.key_project.prover.rules.Taclet taclet,
            SVInstantiations instantiations,
            ImmutableList<AssumesFormulaInstantiation> assumesInstantiations,
            Services services) {
        Debug.assertTrue(ifInstsCorrectSize(taclet, assumesInstantiations),
            "If instantiations list has wrong size");

        SVInstantiations inst = resolveCollisionVarSV(taclet, instantiations, services);
        if (checkVarCondNotFreeIn(taclet, inst, null)) {
            return new NoPosTacletApp(taclet, inst, assumesInstantiations);
        }
        return null;
    }

    public static NoPosTacletApp createNoPosTacletApp(Taclet taclet, MatchResultInfo matchCond,
            Services services) {
        return createNoPosTacletApp(taclet, matchCond.getInstantiations(), null, services);
    }

    /**
     * Create TacletApp with immutable "instantiations", i.e. this instantiations must not be
     * modified later (e.g. by "addInstantiation"). However, this information is currently only used
     * to decide about introduction of metavariables. Immutable instantiations are important for the
     * "addrules" part of taclets.
     */
    public static NoPosTacletApp createFixedNoPosTacletApp(
            org.key_project.prover.rules.Taclet taclet,
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
    protected NoPosTacletApp(org.key_project.prover.rules.Taclet taclet) {
        super(taclet);
    }

    /**
     * creates a NoPosTacletApp for the given taclet with some known instantiations
     *
     * @param taclet the Taclet
     * @param instantiations the SVInstantiations
     */
    private NoPosTacletApp(org.key_project.prover.rules.Taclet taclet,
            SVInstantiations instantiations,
            ImmutableList<AssumesFormulaInstantiation> ifInstantiations) {
        super(taclet, instantiations, ifInstantiations);
    }

    /**
     * adds a new instantiation to this TacletApp
     *
     * @param sv the SchemaVariable to be instantiated
     * @param se the SyntaxElement (usually a {@link Term} or {@link ProgramElement})
     *        with which the SV is instantiated
     * @param interesting a marker whether the instantiation needs to be stored explicitly when
     *        saving a proof; this is usually needed for new names as their creation
     *        is not always deterministic
     * @param services the Services for access to the logic signature and more
     * @return the new TacletApp
     */
    @Override
    public TacletApp addInstantiation(SchemaVariable sv, SyntaxElement se, boolean interesting,
            Services services) {
        if (interesting) {
            return createNoPosTacletApp(taclet(), instantiations().addInteresting(sv, se, services),
                assumesFormulaInstantiations(), services);
        } else {
            return createNoPosTacletApp(taclet(), instantiations().add(sv, se, services),
                assumesFormulaInstantiations(), services);
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
            assumesFormulaInstantiations());
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
        return new NoPosTacletApp(taclet(), svi, assumesFormulaInstantiations());
    }

    /**
     * creates a new Taclet application containing all the instantiations, constraints and new
     * metavariables given by the mc object and forget the old ones
     */
    @Override
    public TacletApp setMatchConditions(MatchResultInfo mc, LogicServices services) {
        return createNoPosTacletApp(taclet(), mc.getInstantiations(),
            assumesFormulaInstantiations(),
            (Services) services);
    }

    /**
     * creates a new Taclet application containing all the instantiations, constraints, new
     * metavariables and if formula instantiations given and forget the old ones
     */
    @Override
    protected TacletApp setAllInstantiations(MatchResultInfo mc,
            ImmutableList<AssumesFormulaInstantiation> assumesInstantiations, Services services) {
        return createNoPosTacletApp(taclet(), mc.getInstantiations(), assumesInstantiations,
            services);
    }

    @Override
    protected Set<QuantifiableVariable> contextVars(SchemaVariable sv) {
        return Collections.emptySet();
    }

    /**
     * returns the PositionInOccurrence (representing a SequentFormula and a position in the
     * corresponding formula)
     *
     * @return the PosInOccurrence
     */
    @Override
    public @Nullable PosInOccurrence posInOccurrence() {
        return null;
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
    public NoPosTacletApp matchFind(PosInOccurrence pos, LogicServices services) {
        return matchFind(null, pos, services);
    }

    /*
     * This is a short-circuit version of matchFind(). It helps eliminate numerous calls to the
     * expensive pos.subTerm() while matching during a recursive descent in a term (where the
     * current subterm is known anyway).
     */
    private NoPosTacletApp matchFind(@Nullable JTerm termToBeMatched, PosInOccurrence pos,
            LogicServices services) {
        if ((termToBeMatched == null) && (pos != null)) {
            termToBeMatched = (JTerm) pos.subTerm();
        }

        MatchResultInfo mc = setupMatchConditions(pos);

        if (mc == null) {
            return null;
        }

        MatchResultInfo res;
        if (taclet() instanceof final FindTaclet findTaclet) {
            res = findTaclet.getMatcher().matchFind(termToBeMatched, mc, services);
            // the following check will partly be repeated within the
            // constructor; this could be optimised
            if (res == null || !checkVarCondNotFreeIn(findTaclet,
                res.getInstantiations(), pos)) {
                return null;
            }
        } else {
            res = mc;
        }
        return evalCheckRes(res, (Services) services);
    }

    private NoPosTacletApp evalCheckRes(MatchResultInfo res, Services services) {
        if (res == null) {
            return null;
        }

        if (updateContextFixed
                && !updateContextCompatible((MatchConditions) res)) {
            return null;
        }

        return (NoPosTacletApp) setMatchConditions(res, services);
    }


    protected MatchResultInfo setupMatchConditions(PosInOccurrence pos) {
        var svInst = taclet() instanceof NoFindTaclet ? instantiations()
                : instantiations().clearUpdateContext();

        MatchConditions mc;
        if (svInst.isEmpty()) {
            mc = MatchConditions.EMPTY_MATCHCONDITIONS;
        } else {
            mc = new MatchConditions(svInst, RenameTable.EMPTY_TABLE);
        }

        if (taclet() instanceof RewriteTaclet rewriteTaclet) {
            mc = rewriteTaclet.checkPrefix(pos, mc);
        }

        return mc;
    }

    private boolean updateContextCompatible(MatchConditions p_mc) {
        return instantiations().getUpdateContext()
                .equals(p_mc.getInstantiations().getUpdateContext());
    }
}
