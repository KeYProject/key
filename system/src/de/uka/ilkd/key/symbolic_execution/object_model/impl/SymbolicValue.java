package de.uka.ilkd.key.symbolic_execution.object_model.impl;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.proof.io.ProofSaver;
import de.uka.ilkd.key.symbolic_execution.object_model.ISymbolicValue;

/**
 * Default implementation of {@link ISymbolicValue}.
 * @author Martin Hentschel
 */
public class SymbolicValue implements ISymbolicValue {
   /**
    * The {@link Services} to use.
    */
   private Services services;
   
   /**
    * The {@link IProgramVariable}.
    */
   private IProgramVariable programVariable;
   
   /**
    * The value {@link Term}.
    */
   private Term value;

   /**
    * Constructor.
    * @param services The {@link Services} to use.
    * @param programVariable The {@link IProgramVariable}.
    * @param value The value {@link Term}.
    */
   public SymbolicValue(Services services, IProgramVariable programVariable, Term value) {
      this.services = services;
      this.programVariable = programVariable;
      this.value = value;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IProgramVariable getProgramVariable() {
      return programVariable;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getProgramVariableString() {
      return programVariable.name() instanceof ProgramElementName ?
             ((ProgramElementName)programVariable.name()).getProgramName() :
             programVariable.name().toString();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Term getValue() {
      return value;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getValueString() {
      StringBuffer sb = ProofSaver.printTerm(value, services, true);
      return sb.toString();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String toString() {
      return "Value of " + getProgramVariableString() + " is " + getValueString();
   }
}