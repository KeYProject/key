package de.uka.ilkd.key.symbolic_execution.model.impl;

import de.uka.ilkd.key.gui.ApplyStrategy;
import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.io.ProofSaver;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionValue;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionVariable;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil.SiteProofVariableValueInput;

/**
 * The default implementation of {@link IExecutionVariable}.
 * @author Martin Hentschel
 */
public class ExecutionVariable extends AbstractExecutionElement implements IExecutionVariable {
   /**
    * The represented {@link IProgramVariable} which value is shown.
    */
   private IProgramVariable programVariable;
   
   /**
    * The parent {@link ExecutionValue} or {@code null} if not available.
    */
   private ExecutionValue parentValue;
   
   /**
    * The index in the parent array.
    */
   private int arrayIndex;

   /**
    * The child {@link IExecutionValue}.
    */
   private ExecutionValue value;

   /**
    * Constructor for a "normal" value.
    * @param mediator The used {@link KeYMediator} during proof.
    * @param proofNodeThe {@link Node} of KeY's proof tree which is represented by this {@link IExecutionNode}.
    * @param programVariable The represented {@link IProgramVariable} which value is shown.
    */
   public ExecutionVariable(KeYMediator mediator, Node proofNode, IProgramVariable programVariable) {
      this(mediator, proofNode, null, programVariable);
   }
   
   /**
    * Constructor for a "normal" child value.
    * @param mediator The used {@link KeYMediator} during proof.
    * @param proofNodeThe {@link Node} of KeY's proof tree which is represented by this {@link IExecutionNode}.
    * @param parentValue The parent {@link ExecutionValue} or {@code null} if not available.
    * @param programVariable The represented {@link IProgramVariable} which value is shown.
    */
   public ExecutionVariable(KeYMediator mediator, Node proofNode, ExecutionValue parentValue, IProgramVariable programVariable) {
      super(mediator, proofNode);
      assert programVariable != null;
      this.parentValue = parentValue;
      this.programVariable = programVariable;
      this.arrayIndex = -1;
   }
   
   /**
    * Constructor for an array cell value.
    * @param mediator The used {@link KeYMediator} during proof.
    * @param proofNodeThe {@link Node} of KeY's proof tree which is represented by this {@link IExecutionNode}.
    * @param parentValue The parent {@link ExecutionValue} or {@code null} if not available.
    * @param arrayIndex The index in the parent array.
    */
   public ExecutionVariable(KeYMediator mediator, Node proofNode, ExecutionValue parentValue, int arrayIndex) {
      super(mediator, proofNode);
      this.parentValue = parentValue;
      this.arrayIndex = arrayIndex;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected String lazyComputeName() throws ProofInputException {
      IProgramVariable pv = getProgramVariable();
      if (pv != null) {
         if (pv.name() instanceof ProgramElementName) {
            ProgramElementName name = (ProgramElementName)pv.name();
            if (SymbolicExecutionUtil.isStaticVariable(getProgramVariable())) {
               return name.toString();
            }
            else {
               return name.getProgramName();
            }
         }
         else {
            return pv.name().toString();
         }
      }
      else {
         if (parentValue != null && parentValue.getVariable() != null) {
            return parentValue.getVariable().getName() + "[" + arrayIndex + "]";
         }
         else {
            return null;
         }
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ExecutionValue getValue() throws ProofInputException {
      synchronized (this) {
         if (value == null) {
            value = lazyComputeValue();
         }
         return value;
      }
   }
   
   /**
    * Computes the value for {@link #getValue()}
    * lazily when the method is called the first time.
    * @throws ProofInputException Occurred Exception.
    */
   protected ExecutionValue lazyComputeValue() throws ProofInputException {
      // Start site proof to extract the value of the result variable.
      SiteProofVariableValueInput sequentToProve;
      Term unknownCheckSelectTerm = null;
      if (getParentValue() != null || SymbolicExecutionUtil.isStaticVariable(getProgramVariable())) {
         unknownCheckSelectTerm = createSelectTerm();
         sequentToProve = SymbolicExecutionUtil.createExtractTermSequent(getServices(), getProofNode(), unknownCheckSelectTerm);
      }
      else {
         sequentToProve = SymbolicExecutionUtil.createExtractVariableValueSequent(getServices(), getProofNode(), getProgramVariable());
      }
      ApplyStrategy.ApplyStrategyInfo info = SymbolicExecutionUtil.startSideProof(getProof(), sequentToProve.getSequentToProve());
      Term value = SymbolicExecutionUtil.extractOperatorValue(info, sequentToProve.getOperator());
      assert value != null;
      // Format return vale
      StringBuffer sb = ProofSaver.printTerm(value, getServices(), true);
      String valueString = sb.toString();
      // Determine type
      String typeString = value.sort().toString();
      // Compute unknown flag if required
      boolean unknownValue = false;
      if (unknownCheckSelectTerm != null) {
         if (SymbolicExecutionUtil.isNullSort(value.sort(), getServices())) { 
            unknownValue = false; // Sort is NullSort, so information must exist in Sequent and value is not unknown
         }
         else {
            unknownValue = SymbolicExecutionUtil.isNotNull(getServices(), getProofNode(), unknownCheckSelectTerm); // Check if the symbolic value is not null, if it fails the value is treated as unknown
            if (unknownValue) {
               value = null; // Reset value
               valueString = null; // Reset value string
               typeString = null; // Reset type
            }
         }
      }
      return new ExecutionValue(getMediator(), 
                                getProofNode(), 
                                this, 
                                unknownValue, 
                                value, 
                                valueString, 
                                typeString);
   }
   
   /**
    * Creates recursive a term which can be used to determine the value
    * of {@link #getProgramVariable()}.
    * @return The created term.
    */
   protected Term createSelectTerm() {
      if (SymbolicExecutionUtil.isStaticVariable(getProgramVariable())) {
         // Static field access
         Function function = getServices().getTypeConverter().getHeapLDT().getFieldSymbolForPV((LocationVariable)getProgramVariable(), getServices());
         return TermBuilder.DF.staticDot(getServices(), getProgramVariable().sort(), function);
      }
      else {
         if (getParentValue() == null) {
            // Direct access to a variable, so return it as term
            return TermBuilder.DF.var((ProgramVariable)getProgramVariable());
         }
         else {
            Term parentTerm = getParentValue().getVariable().createSelectTerm();
            if (programVariable != null) {
               if (getServices().getJavaInfo().getArrayLength() == getProgramVariable()) {
                  // Special handling for length attribute of arrays
                  Function function = getServices().getTypeConverter().getHeapLDT().getLength();
                  return TermBuilder.DF.func(function, parentTerm);
               }
               else {
                  // Field access on the parent variable
                  Function function = getServices().getTypeConverter().getHeapLDT().getFieldSymbolForPV((LocationVariable)getProgramVariable(), getServices());
                  return TermBuilder.DF.dot(getServices(), getProgramVariable().sort(), parentTerm, function);
               }
            }
            else {
               // Special handling for array indices.
               Term idx = TermBuilder.DF.zTerm(getServices(), "" + arrayIndex);
               return TermBuilder.DF.dotArr(getServices(), parentTerm, idx);
            }
         }
      }
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
   public int getArrayIndex() {
      return arrayIndex;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isArrayIndex() {
      return getArrayIndex() >= 0;
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public String getElementType() {
      return "Variable";
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ExecutionValue getParentValue() {
      return parentValue;
   }
}
