package de.uka.ilkd.key.loopinvgen;

import java.util.HashSet;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.DependenciesLDT;
import org.key_project.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.ElementaryUpdate;
import de.uka.ilkd.key.logic.op.EventUpdate;
import de.uka.ilkd.key.logic.op.JFunction;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.logic.op.UpdateJunctor;
import de.uka.ilkd.key.logic.op.UpdateableOperator;
import de.uka.ilkd.key.proof.Goal;

public class RelaxedShiftUpdateImpl {
	private final Goal goal;
	private final Services services;
	private final TermBuilder tb;
	private Term keepParallelUpdateRenames;


	public RelaxedShiftUpdateImpl(Goal g) {
		goal = g;
		services = g.proof().getServices();
		tb = services.getTermBuilder();
		keepParallelUpdateRenames = null;
	}

	public void shiftUpdate(Goal g, PosInOccurrence pos) {

		final Term loopFormula = pos.sequentFormula().formula();
		g.removeFormula(pos);

		final Term renameUpdate = generateRenameUpdate(loopFormula);

		// rename all existing formulas in sequent except program formula
		renameFormulasOnSemisequent(renameUpdate, g.sequent().antecedent(), true);
		renameFormulasOnSemisequent(renameUpdate, g.sequent().succedent(), false);
//		System.out.println("After rename: "+ g.sequent());

		doShift(renameUpdate, g, pos, loopFormula);
//		System.out.println("After complete shift: "+ g.sequent());
		// add program formula again
		g.addFormula(new SequentFormula(UpdateApplication.getTarget(loopFormula)), pos.isInAntec(), true);
//		System.out.println("Putting program back: "+ g.sequent());
	}

	/**
	 * assumes that the current sequent of the goal contains already all formulas
	 * prefixed with the renaming update the method then generates for each
	 * elementary update <code>lhs:=rhs</code> the equation
	 * <code>lhs == {renamingUpdate}{lhs:=rhs}lhs</code> and for each event update
	 * <code>\event(kind,ls,ts)</code> the formula
	 * <code>{renamingUpdate}'kindPred'({\invEvent(kind,ls,ts)}{\event(kind, ls , ts)}ls,t)</code>
	 * where <code>kindPred</code> is the corresponding dependence predicate for the
	 * kind (read or write) of the event update
	 *
	 * @param renameUpdate the {@link Term} representing the renaming update
	 * @param g            the current {@link Goal}
	 * @param pos          the {@link PosInOccurrence} of the loopFormula
	 * @param loopFormula  the {@link Term} representing the formula containing the
	 *                     loop
	 */
	private void doShift(final Term renameUpdate, Goal g, PosInOccurrence pos, final Term loopFormula) {
		ImmutableList<Term> updateList = ImmutableSLList.<Term>nil().prepend(UpdateApplication.getUpdate(loopFormula));
		DependenciesLDT depLDT = services.getTypeConverter().getDependenciesLDT();
		Term counter = tb.zero();
		while (!updateList.isEmpty()) {
			final Term update = updateList.head();
			updateList = updateList.tail();
			if (update.op() instanceof ElementaryUpdate) {
				shiftElementaryUpdate(update, renameUpdate);
			} else if (update.op() instanceof EventUpdate) {
				Operator kind = update.sub(0).op();
//				final Function readMarker = depLDT.getReadMarker();
//				final Function writeMarker = depLDT.getWriteMarker();
//				counter = kind == readMarker || kind == writeMarker ? tb.add(counter, tb.one())
//						: tb.ife(
//								tb.or(tb.equals(update.sub(0), tb.func(readMarker)),
//										tb.equals(update.sub(0), tb.func(writeMarker))),
//								tb.add(counter, tb.one()), counter);
				shiftEventUpdate(update, counter);
			} else if (update.op() == UpdateJunctor.SKIP) {
				// intentionally empty
			} else if (update.op() == UpdateJunctor.PARALLEL_UPDATE) {
				updateList = updateList.prepend(update.sub(0)).prepend(update.sub(1));
			}
		}
	}

	/**
	 * constructs the renaming update for the loop formula. It assumes the the loop
	 * formula has the shape
	 * <code>{l1:=r2 || ... || ln:=rn || eventupdates} and constructs an update that
	 * renames each left-hand side of the elementary update <code>li:=ri</code>
	 *
	 * @param loopFormula the {@link Term} with formula containing the loop
	 * @return a parallel update
	 *         <code>{l1:=l1'|| ... || ln:=ln'}{\event(kind,l1,ts),\event(kind,l1',ts),...}</code>
	 *         that renames each left hand side of the original update
	 */
	private Term generateRenameUpdate(Term loopFormula) {
		ImmutableList<Term> updateList = ImmutableSLList.<Term>nil().prepend(UpdateApplication.getUpdate(loopFormula));

		// collect updated locations
		// collect inverseUpdate of each event
		HashSet<UpdateableOperator> updatedLocations = new HashSet<>();
		ImmutableList<Term> inverseEventUpdates = ImmutableSLList.<Term>nil();

		while (!updateList.isEmpty()) {
			final Term update = updateList.head();
			updateList = updateList.tail();
			if (update.op() instanceof ElementaryUpdate) {
				updatedLocations.add(((ElementaryUpdate) update.op()).lhs());
			} else if (update.op() instanceof EventUpdate) {
				inverseEventUpdates = inverseEventUpdates
						.append(tb.invEventUpdate(update.sub(0), update.sub(1), update.sub(2)));
			} else if (update.op() == UpdateJunctor.PARALLEL_UPDATE) {
				updateList = updateList.prepend(update.sub(1)).prepend(update.sub(0));
			}
		}

		// create renaming update
		ImmutableList<Term> renameUpdates = ImmutableSLList.<Term>nil();
		for (UpdateableOperator lhs : updatedLocations) {
			// Defining a fresh constant symbol a'
			final Name freshConsSymb = new Name(tb.newName("f_" + lhs.name().toString(), services.getNamespaces()));
			final Function freshConsFunc = new Function(freshConsSymb, lhs.sort(), true);
			services.getNamespaces().functions().addSafely(freshConsFunc);
			final Term freshCons = tb.func(freshConsFunc);
//			System.out.println("a' is: " + freshCons.toString());
			// Assigning it to a: a := a' and adding to list of rename updates
			renameUpdates = renameUpdates.prepend(tb.elementary(lhs, freshCons));
		}

		keepParallelUpdateRenames = tb.parallel(renameUpdates);
		final Term parallelInversesEvents = tb.parallel(inverseEventUpdates);
		final Term updateRenameAndInverseEvents = tb.sequential(keepParallelUpdateRenames, parallelInversesEvents);
		return updateRenameAndInverseEvents;
	}

	/**
	 * applies the renaming update on each formula of the given semisequent
	 *
	 * @param renameUpdate the {@link Term} representing the renaming update
	 * @param semi         the {@link Semisequent}
	 * @param antec        a boolean being true if the semisequent is the antecedent
	 *                     of {@link #goal}
	 */
	private void renameFormulasOnSemisequent(final Term renameUpdate, Semisequent semi, boolean antec) {
		for (SequentFormula sf : semi) {
//			System.out.println(sf);
			final PosInOccurrence pio = new PosInOccurrence(sf, PosInTerm.getTopLevel(), antec);
			goal.changeFormula(new SequentFormula(tb.apply(renameUpdate, sf.formula())), pio);
		}
	}

	/**
	 * constructs for an elementary update <code>lhs:=rhs</code> the equation
	 * <code>lhs == {renamingUpdate}{lhs:=rhs}lhs</code>
	 *
	 * @param update         a {@link Term} denoting the elementary update (assumes
	 *                       {@link ElementaryUpdate} as top level operator)
	 * @param renamingUpdate the {@link Term} representing the renaming update
	 */
	private void shiftElementaryUpdate(Term update, Term renamingUpdate) {
		ElementaryUpdate eU = (ElementaryUpdate) update.op();// update: a:=t
		Term target = tb.var(eU.lhs()); // a
		// ********** Defining upd which is not an update but an assignment:
		// a={u'}{u}a
		Term u_on_a = tb.apply(update, target);
		Term u_prime_on_u_on_a = tb.apply(renamingUpdate, u_on_a);
		Term a_ass_up_u_a = tb.equals(target, u_prime_on_u_on_a);
		// then it has to be added to the left side
		goal.addFormula(new SequentFormula(a_ass_up_u_a), true, false);
	}

	/**
	 * adds for one event update <code>\event(kind,ls,ts)</code> the formula
	 * <code>{renamingUpdate}'kindPred'({\invEvent(kind,ls,ts)}{\event(kind,ls,ts)}ls,t)</code>
	 * where <code>kindPred</code> is the corresponding dependence predicate for the
	 * kind (read or write) of the event update
	 *
	 * @param eventUpdate    the {@link Term} with an event update at top level
	 * @param counter the {@link Term} is the iteration number for all because we don't want to capture the dependences inside an iteration
	 */

	private void shiftEventUpdate(Term eventUpdate, Term counter) {
		Term updateTS = eventUpdate.sub(2);
		Term locSet = eventUpdate.sub(1);
		Term eventMarker = eventUpdate.sub(0);
		Term inverseEvent = tb.invEventUpdate(eventMarker, locSet, updateTS);
		Term readMarker = tb.func(services.getTypeConverter().getDependenciesLDT().getReadMarker());
		Term cond1 = tb.equals(eventMarker, readMarker);
		Term writeMarker = tb.func(services.getTypeConverter().getDependenciesLDT().getWriteMarker());
		Term cond2 = tb.equals(eventMarker, writeMarker);

		// Generating rPred and wPred
//		final Term linkTerm4EventUpdate =
//				tb.ife(cond1,
//							tb.rPred(
//									tb.apply(inverseEvent,
//											tb.apply(eventUpdate, locSet)),
//									counter),
//				tb.ife(cond2,
//						tb.wPred(
//								tb.apply(inverseEvent,
//										tb.apply(eventUpdate, locSet)),
//								counter), tb.tt()));
		final Term linkTerm4EventUpdate = tb.ife(cond1, tb.rPred(locSet, counter),tb.ife(cond2, tb.wPred(locSet, counter), tb.tt()));
		// Applying the update rename on the rPred and wPred
		goal.addFormula(new SequentFormula(tb.apply(keepParallelUpdateRenames, linkTerm4EventUpdate)), true, true);
	}

}
