package de.uka.ilkd.key.symbolic_execution.model.impl;

import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.java.TypeConverter;
import de.uka.ilkd.key.java.abstraction.ClassType;
import de.uka.ilkd.key.java.abstraction.Field;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.declaration.ArrayDeclaration;
import de.uka.ilkd.key.java.declaration.TypeDeclaration;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionValue;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionVariable;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;

/**
 * The default implementation of {@link IExecutionValue}.
 * @author Martin Hentschel
 */
public class ExecutionValue extends AbstractExecutionElement implements IExecutionValue {
   /**
    * The parent {@link IExecutionVariable} which provides this {@link IExecutionValue}.
    */
   private ExecutionVariable variable;
   
   /**
    * Is the value unknown?
    */
   private boolean valueUnknown;
   
   /**
    * The value.
    */
   private Term value;
   
   /**
    * The value as human readable {@link String}.
    */
   private String valueString;
   
   /**
    * The type of the value.
    */
   private String typeString;

   /**
    * The child {@link IExecutionVariable}s.
    */
   private ExecutionVariable[] childVariables;

   /**
    * Constructor.
    * @param mediator The used {@link KeYMediator} during proof.
    * @param proofNode The {@link Node} of KeY's proof tree which is represented by this {@link IExecutionNode}.
    * @param variable
    * @param valueUnknown
    * @param value
    * @param valueString
    * @param typeString
    */
   public ExecutionValue(KeYMediator mediator, 
                         Node proofNode, 
                         ExecutionVariable variable, 
                         boolean valueUnknown, 
                         Term value, 
                         String valueString,
                         String typeString) {
      super(mediator, proofNode);
      assert variable != null;
      this.variable = variable;
      this.valueUnknown = valueUnknown;
      this.value = value;
      this.valueString = valueString;
      this.typeString = typeString;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ExecutionVariable getVariable() {
      return variable;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isValueUnknown() throws ProofInputException {
      return valueUnknown;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Term getValue() throws ProofInputException {
      return value;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getValueString() throws ProofInputException {
      return valueString;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isValueAnObject() throws ProofInputException {
      if (isValueUnknown()) {
         return false;
      }
      else {
         Term value = getValue();
         Sort sort = value.sort();
         KeYJavaType kjt = getServices().getJavaInfo().getKeYJavaType(sort);
         TypeConverter typeConverter = getServices().getTypeConverter();
         return typeConverter.isReferenceType(kjt) && // Check if the value is a reference type
                (!(kjt.getJavaType() instanceof TypeDeclaration) || // check if the value is a library class which should be ignored
                !((TypeDeclaration)kjt.getJavaType()).isLibraryClass());
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getTypeString() throws ProofInputException {
      return typeString;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ExecutionVariable[] getChildVariables() throws ProofInputException {
      synchronized (this) {
         if (childVariables== null) {
            childVariables = lazyComputeChildVariables();
         }
         return childVariables;
      }
   }
   
   /**
    * Computes the contained child variables lazily when {@link #getChildVariables()} is called the first time.
    * @return The contained child {@link IExecutionVariable}s.
    * @throws ProofInputException Occurred Exception.
    */
   protected ExecutionVariable[] lazyComputeChildVariables() throws ProofInputException {
      List<ExecutionVariable> children = new LinkedList<ExecutionVariable>();
      Term value = getValue();
      if (value != null && !isValueUnknown()) { // Don't show children of unknown values
         Sort valueSort = value.sort();
         if (valueSort != getServices().getJavaInfo().getNullType().getSort()) {
            KeYJavaType keyType = getServices().getJavaInfo().getKeYJavaType(valueSort);
            Type javaType = keyType.getJavaType();
            if (javaType instanceof ArrayDeclaration) {
               // Array value
               ArrayDeclaration ad = (ArrayDeclaration)javaType;
               Set<IProgramVariable> pvs = SymbolicExecutionUtil.getProgramVariables(ad.length());
               if (pvs.size() == 1) {
                  ExecutionVariable lengthVariable = new ExecutionVariable(getMediator(), getProofNode(), this, pvs.iterator().next());
                  children.add(lengthVariable);
                  try {
                     int length = Integer.valueOf(lengthVariable.getValue().getValueString());
                     for (int i = 0; i < length; i++) {
                        ExecutionVariable childI = new ExecutionVariable(getMediator(), getProofNode(), this, i);
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
                        children.add(new ExecutionVariable(getMediator(), getProofNode(), this, field.getProgramVariable()));
                     }
                  }
               }
            }
         }
      }
      return children.toArray(new ExecutionVariable[children.size()]); 
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected String lazyComputeName() throws ProofInputException {
      return "Value of " + getVariable().getName();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getElementType() {
      return "Value";
   }
}
