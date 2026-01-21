package de.uka.ilkd.key.speclang;

import java.util.function.UnaryOperator;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.modifier.VisibilityModifier;
import de.uka.ilkd.key.logic.Term;

import javax.annotation.Nullable;


/**
 * Common superinterface of all constructs created by the specification language front ends and
 * managed by SpecificationRepository.
 */
public interface SpecificationElement {

    /**
     * Returns the unique internal name of the specification element.
     */
    public String getName();

    /**
     * Returns the displayed name.
     */
    public String getDisplayName();

    /**
     * Returns the visibility of the invariant (null for default visibility)
     */
    public @Nullable VisibilityModifier getVisibility();


    /**
     * Returns the KeYJavaType representing the class/interface to which the specification element
     * belongs.
     */
    public KeYJavaType getKJT();

    /**
     * Applies a unary operator to every term in this specification element.
     *
     * @param op the operator to apply.
     * @param services services.
     * @return this specification element with the operator applied.
     */
    public SpecificationElement map(UnaryOperator<Term> op, Services services);
}
