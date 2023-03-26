package de.uka.ilkd.key.logic.op;


import org.key_project.util.EqualsModProofIrrelevancy;

/**
 * This interface represents the variables that can be bound (by quantifiers or other binding
 * operators).
 */
public interface QuantifiableVariable extends ParsableVariable, EqualsModProofIrrelevancy {
}
