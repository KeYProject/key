/**
 * <p>
 * provides a representation for the term and sequent
 * structure. The structure of a term is defined in {@link
 * de.uka.ilkd.key.logic.Term}. Subclasses of {@link
 * de.uka.ilkd.key.logic.Term} provide representations for special
 * kinds of terms. However, these subclasses are supposed to be not
 * directly accessed. Instead, {@link de.uka.ilkd.key.logic.Term}
 * provides methods for all the methods of the
 * subclasses. Moreover, {@link de.uka.ilkd.key.logic.Term}s (or
 * their subclasses) are supposed to be never constructed by
 * constructors of their own, but by instances of {@link
 * de.uka.ilkd.key.logic.TermFactory}.
 * </p>
 * <p>
 * The function of {@link de.uka.ilkd.key.logic.Term}s (e.g., if
 * they represent a conjunction of subterms, a quantified
 * formula,...) is only determined by an {@link
 * de.uka.ilkd.key.logic.op.Operator} that is assigned to a {@link
 * de.uka.ilkd.key.logic.Term} when the {@link
 * de.uka.ilkd.key.logic.Term} is constructed.
 * </p>
 * <p>
 * {@link de.uka.ilkd.key.logic.Sequent}s consist of two {@link
 * de.uka.ilkd.key.logic.Semisequent}s which represent a
 * duplicate-free list of a {@link
 * de.uka.ilkd.key.logic.SequentFormula}s. The latter consist of
 * a {@link de.uka.ilkd.key.logic.Constraint} and a {@link
 * de.uka.ilkd.key.logic.Term} of a special sort {@link
 * de.uka.ilkd.key.logic.sort.Sort#FORMULA}.
 * </p>
 * <p>
 * {@link de.uka.ilkd.key.logic.Sequent}s and {@link
 * de.uka.ilkd.key.logic.Term}s are <b>immutable</b>.
 * <p>
 * <!-- Created: Fri May 12 13:04:53 MET DST 2000 -->
 * <!-- hhmts start -->
 * Last modified: Wed Dec 4 15:11:14 MET 2002
 * <!-- hhmts end -->
 */
package de.uka.ilkd.key.logic;
