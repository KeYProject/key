package de.uka.ilkd.key.symbolic_execution.object_model.impl;

import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.symbolic_execution.object_model.ISymbolicAssociation;
import de.uka.ilkd.key.symbolic_execution.object_model.ISymbolicObject;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;

/**
 * Default implementation of {@link ISymbolicAssociation}.
 * @author Martin Hentschel
 */
public class SymbolicAssociation implements ISymbolicAssociation {
   /**
    * The {@link IProgramVariable}.
    */
   private IProgramVariable programVariable;
   
   /**
    * The target {@link ISymbolicObject}.
    */
   private ISymbolicObject target;

   /**
    * Constructor.
    * @param programVariable The {@link IProgramVariable}.
    * @param target The target {@link ISymbolicObject}.
    */
   public SymbolicAssociation(IProgramVariable programVariable, ISymbolicObject target) {
      this.programVariable = programVariable;
      this.target = target;
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
   public ISymbolicObject getTarget() {
      return target;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String toString() {
      return "Association " + getProgramVariableString() + " to " + getTarget();
   }
}