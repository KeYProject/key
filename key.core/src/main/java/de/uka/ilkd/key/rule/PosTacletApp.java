/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule;

import java.util.Iterator;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.util.Debug;

import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.prover.rules.instantiation.AssumesFormulaInstantiation;
import org.key_project.prover.rules.instantiation.MatchResultInfo;
import org.key_project.prover.rules.instantiation.SVInstantiations;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSet;

/**
 * A position taclet application object, contains already the information to which term/formula of
 * the sequent the taclet is attached. The position information has been determined by matching the
 * find-part of the corresponding taclet against the term described by the position information. If
 * such a match has not been performed or a taclet is a no find taclet, a no position taclet object
 * ({@link NoPosTacletApp}) is used to keep track of the (partial)
 * instantiation information.
 */
public class PosTacletApp extends TacletApp {

    /**
     * stores the information where the Taclet is to be applied. This means where the find section
     * of the taclet matches
     */
    private final PosInOccurrence pos;

    /**
     * creates a PosTacletApp for the given taclet with some known instantiations and a position
     * information and CHECKS variable conditions as well as it resolves collisions The
     * ifInstantiations parameter is not matched against the assumes-sequence, but only stored. For
     * matching use the method "setAssumesFormulaInstantiations".
     *
     * @param taclet the FindTaclet
     * @param instantiations the SVInstantiations
     * @param pos the PosInOccurrence storing the position where to apply the Taclet
     * @return new PosTacletApp or null if conditions (assertions) have been hurt
     */
    public static PosTacletApp createPosTacletApp(FindTaclet taclet,
            SVInstantiations instantiations, PosInOccurrence pos, Services services) {
        return createPosTacletApp(taclet, instantiations, null, pos, services);
    }

    public static PosTacletApp createPosTacletApp(FindTaclet taclet,
            SVInstantiations instantiations,
            ImmutableList<AssumesFormulaInstantiation> ifInstantiations,
            PosInOccurrence pos, Services services) {
        Debug.assertTrue(ifInstsCorrectSize(taclet, ifInstantiations),
            "If instantiations list has wrong size");

        instantiations = resolveCollisionWithContext(taclet,
            resolveCollisionVarSV(taclet, instantiations, services), pos, services);
        if (checkVarCondNotFreeIn(taclet, instantiations, pos)) {
            return new PosTacletApp(taclet, instantiations, ifInstantiations, pos);
        }

        return null;
    }

    public static PosTacletApp createPosTacletApp(FindTaclet taclet, MatchResultInfo matchCond,
            PosInOccurrence pos, Services services) {
        return createPosTacletApp(taclet, matchCond.getInstantiations(), null, pos, services);
    }

    /**
     * creates a PosTacletApp for the given taclet with some known instantiations and a position
     * information
     *
     * @param taclet the FindTaclet
     * @param instantiations the SVInstantiations
     * @param pos the PosInOccurrence storing the position where to apply the Taclet
     */
    private PosTacletApp(FindTaclet taclet, SVInstantiations instantiations,
            ImmutableList<AssumesFormulaInstantiation> ifInstantiations, PosInOccurrence pos) {
        super(taclet, instantiations, ifInstantiations);
        this.pos = pos;
    }


    /**
     * returns the LogicVariables that are bound above the PositionInOccurrence of the PosTacletApp.
     * __OPTIMIZE__ If this method is needed more than once caching the result should be considered.
     *
     * @return the set of the logicvariables that are bound for the indicated application position
     *         of the TacletApp.
     */
    private static ImmutableSet<QuantifiableVariable> varsBoundAboveFindPos(Taclet taclet,
            PosInOccurrence pos) {

        if (!(taclet instanceof RewriteTaclet)) {
            return DefaultImmutableSet.nil();
        }

        return collectBoundVarsAbove(pos);
    }

    private static Iterator<SchemaVariable> allVariableSV(Taclet taclet) {
        TacletVariableSVCollector coll = new TacletVariableSVCollector();
        coll.visit(taclet, true); // __CHANGE__ true or false???
        return coll.varIterator();
    }


    @Override
    protected ImmutableSet<QuantifiableVariable> contextVars(SchemaVariable sv) {
        if (!taclet().getPrefix(sv).context()) {
            return DefaultImmutableSet.nil();
        }
        return varsBoundAboveFindPos(taclet(), posInOccurrence());
    }


    /**
     * resolves collisions with the context in an SVInstantiation
     *
     * @param insts the original SVInstantiations
     * @return the resolved SVInstantiations
     */
    private static SVInstantiations resolveCollisionWithContext(Taclet taclet,
            SVInstantiations insts, PosInOccurrence pos, Services services) {

        if (taclet.isContextInPrefix()) {
            ImmutableSet<QuantifiableVariable> k = varsBoundAboveFindPos(taclet, pos);
            Iterator<SchemaVariable> it = allVariableSV(taclet);
            while (it.hasNext()) {
                SchemaVariable varSV = it.next();
                JTerm inst = (JTerm) insts.getInstantiation(varSV);
                if (inst != null && k.contains(inst.op())) {
                    insts = replaceInstantiation(taclet, insts, varSV, services);
                }
            }
        }
        return insts;
    }


    /**
     * adds a new instantiation to this TacletApp
     *
     * @param sv the SchemaVariable to be instantiated
     * @param term the Term the SchemaVariable is instantiated with
     * @return the new TacletApp
     */
    @Override
    public TacletApp addInstantiation(SchemaVariable sv, JTerm term, boolean interesting,
            Services services) {

        if (interesting) {
            return createPosTacletApp((FindTaclet) taclet(),
                instantiations().addInteresting(sv, term, services), assumesFormulaInstantiations(),
                posInOccurrence(), services);
        } else {
            return createPosTacletApp((FindTaclet) taclet(),
                instantiations().add(sv, term, services), assumesFormulaInstantiations(),
                posInOccurrence(), services);
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
            return createPosTacletApp((FindTaclet) taclet(),
                instantiations().addInteresting(sv, pe, services), assumesFormulaInstantiations(),
                posInOccurrence(), services);
        } else {
            return createPosTacletApp((FindTaclet) taclet(), instantiations().add(sv, pe, services),
                assumesFormulaInstantiations(), posInOccurrence(), services);
        }
    }

    /**
     * creates a new Taclet application containing all the instantiations given by the
     * SVInstantiations and the ones of this TacletApp
     *
     * @param svi the SVInstantiations whose entries are the needed instantiations
     * @return the new Taclet application
     */
    @Override
    public TacletApp addInstantiation(SVInstantiations svi, Services services) {
        return createPosTacletApp((FindTaclet) taclet(), svi.union(instantiations(), services),
            assumesFormulaInstantiations(), posInOccurrence(), services);
    }


    /**
     * creates a new Taclet application containing all the instantiations given by the
     * SVInstantiations and forget the old ones.
     *
     * @param svi the SVInstantiations whose entries are the needed instantiations
     * @return the new Taclet application
     */
    @Override
    protected TacletApp setInstantiation(SVInstantiations svi, Services services) {
        return createPosTacletApp((FindTaclet) taclet(), svi, assumesFormulaInstantiations(),
            posInOccurrence(), services);
    }


    /**
     * creates a new Taclet application containing all the instantiations, constraints and new
     * metavariables given by the mc object and forget the old ones
     */
    @Override
    public TacletApp setMatchConditions(MatchResultInfo mc, Services services) {
        return createPosTacletApp((FindTaclet) taclet(), mc.getInstantiations(),
            assumesFormulaInstantiations(), posInOccurrence(), services);
    }


    /**
     * creates a new Taclet application containing all the instantiations, constraints, new
     * metavariables and if formula instantiations given and forget the old ones
     */
    @Override
    protected TacletApp setAllInstantiations(MatchResultInfo mc,
            ImmutableList<AssumesFormulaInstantiation> assumesInstantiations,
            Services services) {
        return createPosTacletApp((FindTaclet) taclet(),
            mc.getInstantiations(), assumesInstantiations,
            posInOccurrence(), services);
    }


    /**
     * returns true iff all necessary information is collected, so that the Taclet can be applied.
     *
     * @return true iff all necessary information is collected, so that the Taclet can be applied.
     */
    @Override
    public boolean complete() {
        return posInOccurrence() != null && uninstantiatedVars().isEmpty()
                && assumesInstantionsComplete();
    }

    /**
     * returns the PositionInOccurrence (representing a SequentFormula and a position in the
     * corresponding formula)
     *
     * @return the PosInOccurrence
     */
    @Override
    public PosInOccurrence posInOccurrence() {
        return pos;
    }

    @Override
    public boolean equals(Object o) {
        if (!super.equals(o)) {
            return false;
        }
        return ((PosTacletApp) o).posInOccurrence().equals(posInOccurrence());
    }

    @Override
    public int hashCode() {
        return super.hashCode() + 13 * posInOccurrence().hashCode();
    }

    @Override
    public String toString() {
        return super.toString() + " at " + posInOccurrence();
    }
}
