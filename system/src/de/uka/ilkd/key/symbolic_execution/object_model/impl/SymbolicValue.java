package de.uka.ilkd.key.symbolic_execution.object_model.impl;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.io.ProofSaver;
import de.uka.ilkd.key.symbolic_execution.object_model.ISymbolicValue;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;

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
    * The array index.
    */
   private int arrayIndex;
   
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
    * @param arrayIndex The array index.
    * @param value The value {@link Term}.
    */
   public SymbolicValue(Services services, int arrayIndex, Term value) {
      assert services != null;
      assert arrayIndex >= 0;
      this.services = services;
      this.arrayIndex = arrayIndex;
      this.value = value;
   }

   /**
    * Constructor.
    * @param services The {@link Services} to use.
    * @param programVariable The {@link IProgramVariable}.
    * @param value The value {@link Term}.
    */
   public SymbolicValue(Services services, IProgramVariable programVariable, Term value) {
      assert services != null;
      assert programVariable != null;
      this.services = services;
      this.programVariable = programVariable;
      this.value = value;
      this.arrayIndex = -1;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getName() {
      if (isArrayIndex()) {
         return "[" + getArrayIndex() + "]";
      }
      else {
         return getProgramVariableString();
      }
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isArrayIndex() {
      return arrayIndex >= 0;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public int getArrayIndex() {
      return arrayIndex;
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
      return SymbolicExecutionUtil.getDisplayString(programVariable);
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
   public Sort getType() {
      return value != null ? value.sort() : null;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getTypeString() {
      Sort sort = getType();
      return sort != null ? sort.toString() : null;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String toString() {
      return "Value of " + getName() + " is " + getValueString();
   }
}