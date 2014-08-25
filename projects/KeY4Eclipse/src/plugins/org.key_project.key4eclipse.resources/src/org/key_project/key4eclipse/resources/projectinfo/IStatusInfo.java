package org.key_project.key4eclipse.resources.projectinfo;

/**
 * Defines the functionality to check verification progress.
 * @author Martin Hentschel
 */
public interface IStatusInfo {
   /**
    * Checks if the object itself or one of its children is unspecified.
    * @return {@code true} unspecified content contained, {@code false} everything is specified.
    */
   public boolean isUnspecified();
   
   /**
    * Checks if the object itself or one of its children has an open proof.
    * @return {@code true} open proof contained, {@code false} everything is successful proven.
    */
   public boolean hasOpenProof();
   
   /**
    * Checks if the object itself or one of its children is part of a recursion cycle.
    * @return {@code true} proof is part of recursion cycle, {@code false} all proofs are fine or {@code null} if unknown.
    */
   public boolean isPartOfRecursionCycle();
   
   /**
    * Checks if the current proof is based on unproven specifications.
    * @return {@code true} proof is based on unproven specifications, {@code false} all used specifications are proven.
    */
   public boolean hasUnprovenDependencies();
}
