package de.uka.ilkd.key.slicing;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.expression.PassiveExpression;
import de.uka.ilkd.key.java.reference.FieldReference;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;

/**
 * Defines the basic functionality for slicing algorithms.
 * @author Martin Hentschel
 */
public abstract class AbstractSlicer {
   /**
    * Computes the slice.
    * @param seedNode The seed {@link Node} to start slicing at.
    * @param seedLocation The seed {@link SourceElement}.
    * @return The computed slice.
    */
   public ImmutableArray<Node> slice(Node seedNode, SourceElement seedLocation) {
      return slice(seedNode, toTerm(seedNode.proof().getServices(), seedLocation));
   }
   
   /**
    * Computes the slice.
    * @param seedNode The seed {@link Node} to start slicing at.
    * @param seedLocation The seed {@link Term}.
    * @return The computed slice.
    */
   public abstract ImmutableArray<Node> slice(Node seedNode, Term seedLocation);
   
   /**
    * Converts the given {@link SourceElement} into a {@link Term}.
    * @param services The {@link Services} to use.
    * @param sourceElement The {@link SourceElement} to convert.
    * @return The {@link Term} representing the given {@link SourceElement}.
    */
   public Term toTerm(Services services, SourceElement sourceElement) {
      if (sourceElement instanceof PassiveExpression) {
         if (((PassiveExpression) sourceElement).getChildCount() != 1) {
            throw new IllegalStateException();
         }
         sourceElement = ((PassiveExpression) sourceElement).getChildAt(0);
      }
      if (sourceElement instanceof FieldReference) {
         sourceElement = ((FieldReference) sourceElement).getProgramVariable();
      }
      if (sourceElement instanceof ProgramVariable) {
         ProgramVariable programVariable = (ProgramVariable) sourceElement;
         if (SymbolicExecutionUtil.isStaticVariable(programVariable)) {
            // Static field access
            Function function = services.getTypeConverter().getHeapLDT().getFieldSymbolForPV((LocationVariable)programVariable, services);
            return services.getTermBuilder().staticDot(programVariable.sort(), function);
         }
         else {
            return services.getTermBuilder().var(programVariable);
         }
      }
      else {
         throw new IllegalStateException();
      }
   }
}
