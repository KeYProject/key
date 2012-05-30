package de.uka.ilkd.key.symbolic_execution.model.impl;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.gui.ApplyStrategy;
import de.uka.ilkd.key.java.abstraction.ClassType;
import de.uka.ilkd.key.java.abstraction.Field;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.declaration.ArrayDeclaration;
import de.uka.ilkd.key.java.declaration.FieldDeclaration;
import de.uka.ilkd.key.java.declaration.FieldSpecification;
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
    * The type as human readable string.
    */
   private String typeString;
   
   /**
    * The parent {@link ExecutionVariable} or {@code null} if not available.
    */
   private ExecutionVariable parentVariable;

   /**
    * The child {@link IExecutionVariable}s.
    */
   private IExecutionVariable[] childVariables;
   
   /**
    * The index in the parent array.
    */
   private int arrayIndex;

   /**
    * Constructor for a "normal" value.
    * @param proofNodeThe {@link Node} of KeY's proof tree which is represented by this {@link IExecutionNode}.
    * @param parentVariable The parent {@link ExecutionVariable} or {@code null} if not available.
    * @param programVariable The represented {@link IProgramVariable} which value is shown.
    */
   public ExecutionVariable(Node proofNode, IProgramVariable programVariable) {
      this(proofNode, null, programVariable);
   }
   
   /**
    * Constructor for a "normal" child value.
    * @param proofNodeThe {@link Node} of KeY's proof tree which is represented by this {@link IExecutionNode}.
    * @param parentVariable The parent {@link ExecutionVariable} or {@code null} if not available.
    * @param programVariable The represented {@link IProgramVariable} which value is shown.
    */
   public ExecutionVariable(Node proofNode, ExecutionVariable parentVariable, IProgramVariable programVariable) {
      super(proofNode);
      assert programVariable != null;
      this.parentVariable = parentVariable;
      this.programVariable = programVariable;
      this.arrayIndex = -1;
   }
   
   /**
    * Constructor for an array cell value.
    * @param proofNodeThe {@link Node} of KeY's proof tree which is represented by this {@link IExecutionNode}.
    * @param parentVariable The parent {@link ExecutionVariable} or {@code null} if not available.
    * @param arrayIndex The index in the parent array.
    */
   public ExecutionVariable(Node proofNode, ExecutionVariable parentVariable, int arrayIndex) {
      super(proofNode);
      this.parentVariable = parentVariable;
      this.arrayIndex = arrayIndex;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected String lazyComputeName() {
      IProgramVariable pv = getProgramVariable();
      if (pv != null) {
         if (pv.name() instanceof ProgramElementName) {
            ProgramElementName name = (ProgramElementName)pv.name();
            if (isStaticVariable()) {
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
         if (parentVariable != null) {
            return parentVariable.getName() + "[" + arrayIndex + "]";
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
      SiteProofVariableValueInput sequentToProve;
      if (getParentVariable() != null || isStaticVariable()) {
         Term selectTerm = createSelectTerm();
         sequentToProve = SymbolicExecutionUtil.createExtractTermSequent(getServices(), getProofNode(), selectTerm);
      }
      else {
         sequentToProve = SymbolicExecutionUtil.createExtractVariableValueSequent(getServices(), getProofNode(), getProgramVariable());
      }
      ApplyStrategy.ApplyStrategyInfo info = SymbolicExecutionUtil.startSideProof(getProof(), sequentToProve.getSequentToProve());
      value = SymbolicExecutionUtil.extractOperatorValue(info, sequentToProve.getOperator());
      assert value != null;
      // Format return vale
      StringBuffer sb = ProofSaver.printTerm(value, getServices(), true);
      valueString = sb.toString();
      // Determine type
      typeString = value.sort().toString();
   }
   
   /**
    * Creates recursive a term which can be used to determine the value
    * of {@link #getProgramVariable()}.
    * @return The created term.
    */
   protected Term createSelectTerm() {
      if (isStaticVariable()) {
         // Static field access
         Function function = getServices().getTypeConverter().getHeapLDT().getFieldSymbolForPV((LocationVariable)getProgramVariable(), getServices());
         return TermBuilder.DF.staticDot(getServices(), getProgramVariable().sort(), function);
      }
      else {
         if (getParentVariable() == null) {
            // Direct access to a variable, so return it as term
            return TermBuilder.DF.var((ProgramVariable)getProgramVariable());
         }
         else {
            Term parentTerm = parentVariable.createSelectTerm();
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
    * Checks if the modified {@link ProgramVariable} is static or not.
    * @return {@code true} is static, {@code false} is not static or is array cell.
    */
   protected boolean isStaticVariable() {
      return programVariable instanceof ProgramVariable &&
             ((ProgramVariable)programVariable).isStatic();
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
   public String getTypeString() throws ProofInputException {
      if (value == null) {
         lazyComputeValue();
      }
      return typeString;
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public IExecutionVariable[] getChildVariables() throws ProofInputException {
      if (childVariables== null) {
         childVariables = lazyComputeChildVariables();
      }
      return childVariables;
   }
   
   /**
    * Computes the contained child variables lazily when {@link #getChildVariables()} is called the first time.
    * @return The contained child {@link IExecutionVariable}s.
    * @throws ProofInputException Occurred Exception.
    */
   protected IExecutionVariable[] lazyComputeChildVariables() throws ProofInputException {
      List<IExecutionVariable> children = new LinkedList<IExecutionVariable>();
      Sort valueSort = getValue().sort();
      if (valueSort != getServices().getJavaInfo().getNullType().getSort()) {
         KeYJavaType keyType = getServices().getJavaInfo().getKeYJavaType(valueSort);
         Type javaType = keyType.getJavaType();
         if (javaType instanceof ArrayDeclaration) {
            // Array value
            ArrayDeclaration ad = (ArrayDeclaration)javaType;
            Set<IProgramVariable> pvs = getProgramVariables(ad.length());
            if (pvs.size() == 1) {
               ExecutionVariable lengthVariable = new ExecutionVariable(getProofNode(), this, pvs.iterator().next());
               children.add(lengthVariable);
               try {
                  int length = Integer.valueOf(lengthVariable.getValueString());
                  for (int i = 0; i < length; i++) {
                     ExecutionVariable childI = new ExecutionVariable(getProofNode(), this, i);
                     children.add(childI);
                  }
               }
               catch (NumberFormatException e) {
                  // Symbolic value, nothing to do.
               }
            }
         }
         else if (javaType instanceof ClassType) {
            // Normal value
            ImmutableList<Field> fields = ((ClassType)javaType).getAllFields(getServices());
            for (Field field : fields) {
               ImmutableList<ProgramVariable> vars = getServices().getJavaInfo().getAllAttributes(field.getFullName(), keyType);
               for (ProgramVariable var : vars) {
                  if (!var.isImplicit() && !var.isStatic()) {
                     children.add(new ExecutionVariable(getProofNode(), this, field.getProgramVariable()));
                  }
               }
            }
         }
      }
      return children.toArray(new IExecutionVariable[children.size()]); 
   }
   
   /**
    * Collects all {@link IProgramVariable}s of the given {@link FieldDeclaration}.
    * @param fd The given {@link FieldDeclaration}.
    * @return The found {@link IProgramVariable}s for the given {@link FieldDeclaration}.
    */
   protected Set<IProgramVariable> getProgramVariables(FieldDeclaration fd) {
      Set<IProgramVariable> result = new HashSet<IProgramVariable>();
      if (fd != null) {
         ImmutableArray<FieldSpecification> specifications = fd.getFieldSpecifications();
         for (FieldSpecification spec : specifications) {
            result.add(spec.getProgramVariable());
         }
      }
      return result;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ExecutionVariable getParentVariable() {
      return parentVariable;
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
}
