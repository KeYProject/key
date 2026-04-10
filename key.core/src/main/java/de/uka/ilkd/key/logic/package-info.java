/**
 * <p>
 * provides a representation for the term
 * structure. The structure of a term is defined in {@link
 * de.uka.ilkd.key.logic.JTerm}. Subclasses of {@link
 * de.uka.ilkd.key.logic.JTerm} provide representations for special
 * kinds of terms. However, these subclasses are supposed to be not
 * directly accessed. Instead, {@link de.uka.ilkd.key.logic.JTerm}
 * provides methods for all the methods of the
 * subclasses. Moreover, {@link de.uka.ilkd.key.logic.JTerm}s (or
 * their subclasses) are supposed to be never constructed by
 * constructors of their own, but by instances of {@link
 * de.uka.ilkd.key.logic.TermFactory}.
 * </p>
 * <p>
 * The function of {@link de.uka.ilkd.key.logic.JTerm}s (e.g., if
 * they represent a conjunction of subterms, a quantified
 * formula,...) is only determined by an {@link
 * org.key_project.logic.op.Operator} that is assigned to a {@link
 * de.uka.ilkd.key.logic.JTerm} when the {@link
 * de.uka.ilkd.key.logic.JTerm} is constructed.
 * </p>
 * <p>
 * {@link de.uka.ilkd.key.logic.JTerm}s are <b>immutable</b>.
 * <p>
 * <!-- Created: Fri May 12 13:04:53 MET DST 2000 -->
 * <!-- hhmts start -->
 * Last modified: Wed Dec 4 15:11:14 MET 2002
 * <!-- hhmts end -->
 */
package de.uka.ilkd.key.logic;
