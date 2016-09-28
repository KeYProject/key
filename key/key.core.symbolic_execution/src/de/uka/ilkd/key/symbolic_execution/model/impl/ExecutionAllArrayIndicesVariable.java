package de.uka.ilkd.key.symbolic_execution.model.impl;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.ApplyStrategy.ApplyStrategyInfo;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionValue;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionVariable;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionSideProofUtil;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;

/**
 * An implementation of {@link IExecutionVariable} used to query
 * all array indices at the same time. This supports also arrays where
 * the length is symbolic and not a concrete number.
 * @author Martin Hentschel
 */
public class ExecutionAllArrayIndicesVariable extends ExecutionVariable {
   /**
    * The name of the constant used to query the value of all array indices.
    */
   public static final String ARRAY_INDEX_CONSTANT_NAME = "*";
   
   /**
    * The constant representing an arbitrary array index.
    */
   private Term constant;

   /**
    * Constructor.
    * @param parentNode The parent {@link IExecutionNode}.
    * @param proofNode The {@link Node} of KeY's proof tree which is represented by this {@link IExecutionNode}.
    * @param modalityPIO The {@link PosInOccurrence} of the modality of interest.
    * @param parentValue The parent {@link IExecutionValue} representing the array.
    * @param arrayProgramVariable The {@link IProgramVariable} of the array.
    * @param additionalCondition An optional additional condition to consider.
    */
   public ExecutionAllArrayIndicesVariable(IExecutionNode<?> parentNode,
                                           Node proofNode, 
                                           PosInOccurrence modalityPIO, 
                                           ExecutionValue parentValue, 
                                           IProgramVariable arrayProgramVariable,
                                           Term additionalCondition) {
      super(parentNode, 
            proofNode, 
            modalityPIO, 
            parentValue, 
            arrayProgramVariable,
            additionalCondition);
      assert parentValue != null;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected String lazyComputeName() throws ProofInputException {
      // Ensure that constant is defined
      if (constant == null) {
         getValues(); 
      }
      // Compute name
      String arrayName = super.lazyComputeName();
      return arrayName + "[" + constant + "]";
   }

   /**
    * Computes the value for {@link #getValues()}
    * lazily when the method is called the first time.
    * @throws ProofInputException Occurred Exception.
    */
   protected ExecutionValue[] lazyComputeValues() throws ProofInputException {
      InitConfig initConfig = getInitConfig();
      if (initConfig != null) { // Otherwise proof is disposed.
         final ProofEnvironment sideProofEnv = SymbolicExecutionSideProofUtil.cloneProofEnvironmentWithOwnOneStepSimplifier(initConfig, true); // New OneStepSimplifier is required because it has an internal state and the default instance can't be used parallel.
         final Services sideServices = sideProofEnv.getServicesForEnvironment();
         final TermBuilder tb = sideServices.getTermBuilder();
         // Start site proof to extract the value of the result variable.
         Term siteProofCondition = getAdditionalCondition() != null ?
                                   tb.and(getAdditionalCondition(), getParentValue().getCondition()) :
                                   getParentValue().getCondition();
         Term arrayTerm = createArrayTerm();
         // Create index constant
         Function constantFunction = new Function(new Name(tb.newName(ARRAY_INDEX_CONSTANT_NAME)), sideServices.getTypeConverter().getIntegerLDT().targetSort());
         constant = tb.func(constantFunction);
         setName(lazyComputeName()); // Update name because constant has changed
         Term arrayIndex = tb.dotArr(arrayTerm, constant);
         
         // Create predicate which will be used in formulas to store the value interested in.
         Function resultPredicate = new Function(new Name(tb.newName("ResultPredicate")), Sort.FORMULA, arrayIndex.sort());
         Function arrayLengthFunction = sideServices.getTypeConverter().getHeapLDT().getLength();
         Term arrayRange = tb.and(tb.geq(constant, tb.zero()), tb.lt(constant, tb.func(arrayLengthFunction, arrayTerm)));
         // Create formula which contains the value interested in.
         Term resultTerm = tb.func(resultPredicate, arrayIndex);
         Term resultImplication = tb.imp(arrayRange, resultTerm);
         // Create Sequent to prove with new succedent.
         Sequent sequent = SymbolicExecutionUtil.createSequentToProveWithNewSuccedent(getProofNode(), getModalityPIO(), siteProofCondition, resultImplication, false);
         // Perform side proof
         ApplyStrategyInfo info = SymbolicExecutionSideProofUtil.startSideProof(getProof(), 
                                                                                sideProofEnv,
                                                                                sequent, 
                                                                                StrategyProperties.METHOD_NONE,
                                                                                StrategyProperties.LOOP_NONE,
                                                                                StrategyProperties.QUERY_OFF,
                                                                                StrategyProperties.SPLITTING_DELAYED);
         try {
            return instantiateValuesFromSideProof(initConfig, 
                                                  sideServices, 
                                                  tb, 
                                                  info, 
                                                  resultPredicate, 
                                                  arrayTerm, // Pass array to ensure that unknown values are correctly computed.
                                                  siteProofCondition);
         }
         finally {
            SymbolicExecutionSideProofUtil.disposeOrStore("All array indices value computation on node " + getProofNode().serialNr(), info);
         }
      }
      else {
         return null;
      }
   }

   /**
    * Creates a {@link Term} to access the array.
    * @return The {@link Term} to access the array.
    */
   public Term createArrayTerm() {
      return getParentValue().getVariable().createSelectTerm();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Term createSelectTerm() {
      assert constant != null : "Call getValues() before calling createSelectTerm().";
      return getServices().getTermBuilder().dotArr(createArrayTerm(), constant);
   }
}
