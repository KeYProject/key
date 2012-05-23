package de.uka.ilkd.key.symbolic_execution.model.impl;

import java.util.LinkedList;
import java.util.List;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.gui.ApplyStrategy;
import de.uka.ilkd.key.java.abstraction.ClassType;
import de.uka.ilkd.key.java.abstraction.Field;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.reference.IExecutionContext;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.io.ProofSaver;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionVariable;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil.SiteProofVariableValueInput;
import de.uka.ilkd.key.util.MiscTools;

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
    * The value.
    */
   private Term value;
   
   /**
    * The value as human readable string.
    */
   private String valueString;
   
   /**
    * The parent {@link ExecutionVariable} or {@code null} if not available.
    */
   private ExecutionVariable parentVariable;

   /**
    * The child {@link IExecutionVariable}s.
    */
   private IExecutionVariable[] childVariables;

   /**
    * Constructor.
    * @param proofNodeThe {@link Node} of KeY's proof tree which is represented by this {@link IExecutionNode}.
    * @param parentVariable The parent {@link ExecutionVariable} or {@code null} if not available.
    * @param programVariable The represented {@link IProgramVariable} which value is shown.
    */
   public ExecutionVariable(Node proofNode, ExecutionVariable parentVariable, IProgramVariable programVariable) {
      super(proofNode);
      assert programVariable != null;
      this.parentVariable = parentVariable;
      this.programVariable = programVariable;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected String lazyComputeName() {
      IProgramVariable pv = getProgramVariable();
      if (pv != null) {
         if (pv.name() instanceof ProgramElementName) {
            return ((ProgramElementName)pv.name()).getProgramName();
         }
         else {
            return pv.name().toString();
         }
      }
      else {
         return null;
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Term getValue() throws ProofInputException {
      if (value == null) {
         lazyComputeValue();
      }
      return value;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getValueString() throws ProofInputException {
      if (value == null) {
         lazyComputeValue();
      }
      return valueString;
   }
   
   /**
    * Computes the value for {@link #getValue()} and {@link #getValueString()}
    * lazily when one of the method is called the first time.
    * @throws ProofInputException Occurred Exception.
    */
   protected void lazyComputeValue() throws ProofInputException {
      // Start site proof to extract the value of the result variable.
      JavaBlock jb = getProofNode().getAppliedRuleApp().posInOccurrence().subTerm().javaBlock();
      IExecutionContext context = MiscTools.getInnermostExecutionContext(jb, getServices());
      SiteProofVariableValueInput sequentToProve;
      if (getParentVariable() != null) {
         Term selectTerm = createSelectTerm();
         sequentToProve = SymbolicExecutionUtil.createExtractTermSequent(getServices(), context, getProofNode(), selectTerm);
      }
      else {
         sequentToProve = SymbolicExecutionUtil.createExtractVariableValueSequent(getServices(), context, getProofNode(), getProgramVariable());
      }
      ApplyStrategy.ApplyStrategyInfo info = SymbolicExecutionUtil.startSideProof(getProof(), sequentToProve.getSequentToProve());
      value = SymbolicExecutionUtil.extractOperatorValue(info, sequentToProve.getOperator());
      assert value != null;
      // Format return vale
      StringBuffer sb = ProofSaver.printTerm(value, getServices(), true);
      valueString = sb.toString();
   }
   
   /**
    * Creates recursive a term which can be used to determine the value
    * of {@link #getProgramVariable()}.
    * @return The created term.
    */
   protected Term createSelectTerm() {
      if (getParentVariable() == null) {
         // Direct access to a variable, so return it as term
         return TermBuilder.DF.var((ProgramVariable)getProgramVariable());
      }
      else {
         Term parentTerm = parentVariable.createSelectTerm();
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
   public String getTypeString() {
      return programVariable.sort().toString();
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public IExecutionVariable[] getChildVariables() throws ProofInputException {
      if (childVariables== null) {
         List<IExecutionVariable> children = new LinkedList<IExecutionVariable>();
         Sort valueSort = getValue().sort();
         if (valueSort != getServices().getJavaInfo().getNullType().getSort()) {
            KeYJavaType keyType = getServices().getJavaInfo().getKeYJavaType(valueSort);
            Type javaType = keyType.getJavaType();
            if (javaType instanceof ClassType) {
               ImmutableList<Field> fields = ((ClassType)javaType).getAllFields(getServices());
               for (Field field : fields) {
                  ImmutableList<ProgramVariable> vars = getServices().getJavaInfo().getAllAttributes(field.getFullName(), keyType);
                  for (ProgramVariable var : vars) {
                     if (!var.isImplicit()) {
                        children.add(new ExecutionVariable(getProofNode(), this, field.getProgramVariable()));
                     }
                  }
               }
            }
         }
         childVariables = children.toArray(new IExecutionVariable[children.size()]); 
      }
      return childVariables;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ExecutionVariable getParentVariable() {
      return parentVariable;
   }
}
