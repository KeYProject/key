// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.symbolic_execution.model.impl;

import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.java.abstraction.ClassType;
import de.uka.ilkd.key.java.abstraction.Field;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.declaration.ArrayDeclaration;
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
   private final ExecutionVariable variable;
   
   /**
    * Is the value unknown?
    */
   private final boolean valueUnknown;
   
   /**
    * The value.
    */
   private final Term value;
   
   /**
    * The value as human readable {@link String}.
    */
   private final String valueString;
   
   /**
    * The type of the value.
    */
   private final String typeString;

   /**
    * The condition under which the variable has this value.
    */
   private final Term condition;

   /**
    * The condition under which the variable has this value as human readable {@link String}.
    */
   private final String conditionString;

   /**
    * The child {@link IExecutionVariable}s.
    */
   private ExecutionVariable[] childVariables;

   /**
    * Constructor.
    * @param mediator The used {@link KeYMediator} during proof.
    * @param proofNode The {@link Node} of KeY's proof tree which is represented by this {@link IExecutionNode}.
    * @param variable The parent {@link ExecutionVariable} which contains this value.
    * @param valueProofNode The {@link Node} in the value site proof from which this value was extracted.
    * @param valueUnknown Is the value unknown?
    * @param value The value.
    * @param valueString The value as human readable string.
    * @param typeString The type of the value.
    */
   public ExecutionValue(KeYMediator mediator, 
                         Node proofNode, 
                         ExecutionVariable variable,
                         boolean valueUnknown, 
                         Term value, 
                         String valueString,
                         String typeString,
                         Term condition,
                         String conditionString) {
      super(variable.getSettings(), mediator, proofNode);
      this.variable = variable;
      this.valueUnknown = valueUnknown;
      this.value = value;
      this.valueString = valueString;
      this.typeString = typeString;
      this.condition = condition;
      this.conditionString = conditionString;
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
         return SymbolicExecutionUtil.hasReferenceSort(getServices(), value);
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
            if (keyType != null) { // Can be null, e.g. if Sort is the Sort of Heap
               Type javaType = keyType.getJavaType();
               if (javaType instanceof ArrayDeclaration) {
                  // Array value
                  ArrayDeclaration ad = (ArrayDeclaration)javaType;
                  Set<IProgramVariable> pvs = SymbolicExecutionUtil.getProgramVariables(ad.length());
                  if (pvs.size() == 1) {
                     ExecutionVariable lengthVariable = new ExecutionVariable(getVariable().getParentNode(), this, pvs.iterator().next());
                     children.add(lengthVariable);
                     ExecutionValue[] lengthValues = lengthVariable.getValues();
                     for (ExecutionValue lengthValue : lengthValues) {
                        try {
                           int length = Integer.valueOf(lengthValue.getValueString());
                           for (int i = 0; i < length; i++) {
                              ExecutionVariable childI = new ExecutionVariable(getVariable().getParentNode(), this, i, lengthValue);
                              children.add(childI);
                           }
                        }
                        catch (NumberFormatException e) {
                           // Symbolic value, nothing to do.
                        }
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
                           children.add(new ExecutionVariable(getVariable().getParentNode(), this, field.getProgramVariable()));
                        }
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
      String conditionString = getConditionString();
      if (conditionString != null) {
         return getVariable().getName() + " {" + getConditionString() + "}";
      }
      else {
         return getVariable().getName();
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getElementType() {
      return "Value";
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Term getCondition() throws ProofInputException {
      return condition;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getConditionString() throws ProofInputException {
      return conditionString;
   }
}