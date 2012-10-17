package de.uka.ilkd.key.gui.macros;

import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.logic.PosInOccurrence;

/**
 * The interface ProofMacro is the entry point to a general strategy extension
 * system.
 * 
 * <h3>Idea</h3>
 * 
 * Doing interaction with KeY is often tedious, many steps have to be performed
 * over and over again. To facilitate the interaction, this frameworks allows a
 * developer to define "macro strategy steps" which combine many individual
 * steps and are helopful in an interactive verification attempt.
 * 
 * This interface is kept deliberately separate from many of the other
 * mechanisms to remain open on how to implement the macro.
 * 
 * <h3>Usage</h3>
 * 
 * Proof macros are meant to be stateless singletons.
 * 
 * Whenever a situation arises where the user wants to apply macros, they are
 * asked whether they can be applied (
 * {@link #canApplyTo(KeYMediator, PosInOccurrence)}). A macro is offered to the
 * user iff it returns <code>true</code>. No changes should be made there.
 * 
 * A macro is then applied using {@link #applyTo(KeYMediator, PosInOccurrence)}.
 * This may change the proof by applying rule applications. It is allowed to use
 * automatic runs, manual instantiations, ...
 * 
 * A proof macro needs to extract all necessary information on the application
 * from the mediator passed to the
 * {@link #applyTo(KeYMediator, PosInOccurrence)} (or
 * {@link #canApplyTo(KeYMediator, PosInOccurrence)}) method. You will be able
 * to access any interesting data from that starting point, especially
 * {@link KeYMediator#getInteractiveProver()}.
 * 
 * <h3>Registration</h3>
 * 
 * When implementing a new proof macro, no existing code needs to be adapted.
 * Please add the class name of your new implementation to the file
 * <tt>resources/META-INF/services/de.uka.ilkd.key.gui.macros.ProofMacro</tt>.
 * 
 * @see KeYMediator
 * 
 * @author mattias ulbrich
 */
public interface ProofMacro {

    /**
     * Gets the name of this macro.
     * 
     * Used as menu entry
     * 
     * @return a non-<code>null</code> constant string 
     */
    public String getName();

    /**
     * Gets the description of this macro.
     * 
     * Used as tooltip.
     * 
     * @return a non-<code>null</code> constant string 
     */
    public String getDescription();

    /**
     * Can apply this macro be applied?
     * 
     * This method should not make any changes but check if the macro can be
     * applied or not in the given context.
     * 
     * @param mediator
     *            the mediator (not <code>null</code>)
     * @param posInOcc
     *            the position in occurrence (may be <code>null</code>)
     *            
     * @return <code>true</code>, if the macro is allowed to be applied
     */
    public boolean canApplyTo(KeYMediator mediator, PosInOccurrence posInOcc);

    /**
     * Apply this macro
     * 
     * This method can change the proof by applying rules to it.
     * 
     * @param mediator
     *            the mediator (not <code>null</code>)
     * @param posInOcc
     *            the position in occurrence (may be <code>null</code>)
     */
    public void applyTo(KeYMediator mediator, PosInOccurrence posInOcc);
}
