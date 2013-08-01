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


package de.uka.ilkd.key.proof.init;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Properties;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.Modifier;
import de.uka.ilkd.key.java.declaration.ParameterDeclaration;
import de.uka.ilkd.key.java.declaration.VariableSpecification;
import de.uka.ilkd.key.java.expression.literal.NullLiteral;
import de.uka.ilkd.key.java.expression.operator.CopyAssignment;
import de.uka.ilkd.key.java.reference.TypeReference;
import de.uka.ilkd.key.java.statement.Branch;
import de.uka.ilkd.key.java.statement.Catch;
import de.uka.ilkd.key.java.statement.Finally;
import de.uka.ilkd.key.java.statement.TransactionStatement;
import de.uka.ilkd.key.java.statement.Try;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SymbolicExecutionTermLabel;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.speclang.HeapContext;

/**
 * <p>
 * This abstract implementation of {@link ProofOblInput} extends the
 * functionality of {@link AbstractPO} to execute some code within a try catch
 * block.
 * </p>
 * <p>
 * The generated {@link Sequent} has the following form:
 * <pre>
 * <code>
 * ==>
 * &lt;generalAssumptions&gt; &
 * &lt;preconditions&gt;
 * ->
 * &lt;updatesToStoreInitialValues&gt;
 * &lt;modalityStart&gt;
 * exc=null;try {&lt;customCode&gt;}catch(java.lang.Exception e) {exc = e}
 * &lt;modalityEnd&gt;
 * (exc = null & &lt;postconditions &gt; & &lt;optionalUninterpretedPredicate&gt;)
 * </code>
 * </pre>
 * </p>
 * <p>
 * If {@link #isAddUninterpretedPredicate()} an uninterpreted predicate is
 * added to the postcondition which contains the heap and all parameters as
 * argument. This predicate can be used to filter out invalid execution paths
 * because its branches are closed while still open branches contains valid
 * execution paths.
 * </p>
 * @author Martin Hentschel
 */
public abstract class AbstractOperationPO extends AbstractPO {
   /**
    * If this is {@code true} an uninterpreted predicate is added to the
    * postconditions which contains the heap and all parameters as arguments.
    * @see #buildUninterpretedPredicate(ImmutableList, String)
    * @see #getUninterpretedPredicateName()
    */
   private boolean addUninterpretedPredicate;

   /**
    * If this is {@code true} the {@link SymbolicExecutionTermLabel} will be added
    * to the initial modality which is proven.
    */
   private boolean addSymbolicExecutionLabel;

   /**
    * The used uninterpreted predicate created via
    * {@link #buildUninterpretedPredicate(ImmutableList, ProgramVariable, String)}
    * and available via {@link #getUninterpretedPredicate()}.
    */
   private Term uninterpretedPredicate;

   /**
    * Constructor.
    * @param initConfig The {@link InitConfig} to use.
    * @param name The name to use.
    */
   public AbstractOperationPO(InitConfig initConfig, String name) {
      this(initConfig, name, false, false);
   }

   /**
    * Constructor.
    * @param initConfig The {@link InitConfig} to use.
    * @param name he name to use.
    * @param addUninterpretedPredicate {@code true} postcondition contains uninterpreted predicate, {@code false} uninterpreted predicate is not contained in postcondition.
    * @param addSymbolicExecutionLabel {@code true} to add the {@link SymbolicExecutionTermLabel} to the modality, {@code false} to not label the modality.
    */
   public AbstractOperationPO(InitConfig initConfig,
                              String name,
                              boolean addUninterpretedPredicate,
                              boolean addSymbolicExecutionLabel) {
      super(initConfig, name);
      this.addUninterpretedPredicate = addUninterpretedPredicate;
      this.addSymbolicExecutionLabel = addSymbolicExecutionLabel;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void readProblem() throws ProofInputException {
      final IProgramMethod pm = getProgramMethod();
      final boolean[] transactionFlags;
      if (isTransactionApplicable()) {
         transactionFlags = new boolean[] { false, true };
         poNames = new String[2];
      }
      else {
         transactionFlags = new boolean[] { false };
      }
      final List<Term> termPOs = new ArrayList<Term>();
      int nameIndex = 0;
      for (boolean transactionFlag : transactionFlags) {
         // prepare variables, program method, heapAtPre
         boolean makeNamesUnique = isMakeNamesUnique();
         final ImmutableList<ProgramVariable> paramVars = TB.paramVars(services, pm, makeNamesUnique);
         final ProgramVariable selfVar = TB.selfVar(services, pm, getCalleeKeYJavaType(), makeNamesUnique);
         final ProgramVariable resultVar = TB.resultVar(services, pm, makeNamesUnique);
         final ProgramVariable exceptionVar = TB.excVar(services, pm, makeNamesUnique);

         final List<LocationVariable> modHeaps = HeapContext.getModHeaps(services, transactionFlag);
         final Map<LocationVariable, LocationVariable> atPreVars = HeapContext.getBeforeAtPreVars(modHeaps, services, "AtPre");

         final Map<LocationVariable, Map<Term, Term>> heapToAtPre = new LinkedHashMap<LocationVariable, Map<Term, Term>>();

         for (LocationVariable heap : modHeaps) {
            heapToAtPre.put(heap, new LinkedHashMap<Term, Term>());
            heapToAtPre.get(heap).put(TB.var(heap), TB.var(atPreVars.get(heap)));
         }

         // FIXME Wojtek: This is a fiddly bit that needs to be rechecked eventually
         if (modHeaps.contains(getSavedHeap())) {
            heapToAtPre.get(getSavedHeap()).put(TB.getBaseHeap(services), TB.var(atPreVars.get(getSavedHeap())));
         }

         // register the variables so they are declared in proof header if the proof is saved to a file
         register(paramVars);
         register(selfVar);
         register(resultVar);
         register(exceptionVar);
         for (LocationVariable lv : atPreVars.values()) {
            register(lv);
         }

         // create arguments from formal parameters for method call
         ImmutableList<LocationVariable> formalParamVars = ImmutableSLList.<LocationVariable> nil();
         for (ProgramVariable paramVar : paramVars) {
            if (isCopyOfMethodArgumentsUsed()) {
               ProgramElementName pen = new ProgramElementName("_" + paramVar.name());
               LocationVariable formalParamVar = new LocationVariable(pen, paramVar.getKeYJavaType());
               formalParamVars = formalParamVars.append(formalParamVar);
               register(formalParamVar);
            }
            else {
               formalParamVars = formalParamVars.append((LocationVariable)paramVar); // The cast is ugly but legal. It is a bigger task to refactor TB.paramVars to return a list of LocationVariabe instead of ProgramVariable.
            }
         }

         // build program block to execute in try clause (must be done before pre condition is created.
         final ImmutableList<StatementBlock> sb = buildOperationBlocks(formalParamVars, selfVar, resultVar);

         // build precondition
         final Term pre = TB.and(buildFreePre(selfVar, getCalleeKeYJavaType(), paramVars, modHeaps),
                                 getPre(modHeaps, selfVar, paramVars, atPreVars, services));

         // build program term
         Term postTerm = getPost(modHeaps, selfVar, paramVars, resultVar, exceptionVar, atPreVars, services);
         // Add uninterpreted predicate
         if (isAddUninterpretedPredicate()) {
            postTerm = TB.and(postTerm,
                              buildUninterpretedPredicate(paramVars, exceptionVar, getUninterpretedPredicateName()));
         }

         Term frameTerm = buildFrameClause(modHeaps, heapToAtPre, selfVar, paramVars);

         final Term post = TB.and(postTerm, frameTerm);
         final LocationVariable baseHeap = services.getTypeConverter().getHeapLDT().getHeap();
         final Term selfVarTerm = selfVar==null? null: TB.var(selfVar);
         final Term globalUpdate = getGlobalDefs(baseHeap, TB.getBaseHeap(services), selfVarTerm, TB.var(paramVars), services);

         final Term progPost = buildProgramTerm(paramVars, formalParamVars, selfVar, resultVar, exceptionVar, atPreVars, post, sb);
         final Term preImpliesProgPost = TB.imp(pre, progPost);
         final Term applyGlobalUpdate = globalUpdate==null? preImpliesProgPost: TB.apply(globalUpdate, preImpliesProgPost);
         termPOs.add(applyGlobalUpdate);
         if (poNames != null) {
            poNames[nameIndex++] = buildPOName(transactionFlag);
         }
      }
      // save in field
      assignPOTerms(termPOs.toArray(new Term[0]));

      // add axioms
      collectClassAxioms(getCalleeKeYJavaType());
   }

   /**
    * Checks if self variable, exception variable, result variable
    * and method call arguments should be renamed to make sure that their
    * names are unique in the whole KeY application.
    * @return {@code true} use unique names, {@code false} use original names even if they are not unique in whole KeY application.
    */
   protected boolean isMakeNamesUnique() {
      return true;
   }

   /**
    * Returns the {@link IProgramMethod} to call.
    * @return The {@link IProgramMethod} to call.
    */
   protected abstract IProgramMethod getProgramMethod();

   /**
    * Checks if transactions are applicable.
    * @return Transactions are applicable?
    */
   protected abstract boolean isTransactionApplicable();

   /**
    * Returns the {@link KeYJavaType} which contains {@link #getProgramMethod()}.
    * @return The {@link KeYJavaType} which contains {@link #getProgramMethod()}.
    */
   protected abstract KeYJavaType getCalleeKeYJavaType();

   /**
    * Builds the code to execute in different statement blocks.
    * 1. code to execute before the try block
    * 2. code to execute in the try block
    * 3. code to execute in the catch block
    * 4. code to execute in the finally block
    * @param formalParVars Arguments from formal parameters for method call.
    * @param selfVar The self variable.
    * @param resultVar The result variable.
    */
   protected abstract ImmutableList<StatementBlock> buildOperationBlocks(ImmutableList<LocationVariable> formalParVars,
                                                         ProgramVariable selfVar,
                                                         ProgramVariable resultVar);


   @Deprecated
   protected StatementBlock buildOperationBlock(ImmutableList<LocationVariable> formalParVars,
                                                         ProgramVariable selfVar,
                                                         ProgramVariable resultVar) {
       return buildOperationBlocks(formalParVars,selfVar,resultVar).tail().head();
   }

   /**
    * Builds the "general assumption".
    * @param selfVar The self variable.
    * @param selfKJT The {@link KeYJavaType} of the self variable.
    * @param paramVars The parameters {@link ProgramVariable}s.
    * @param heaps The heaps.
    * @return The {@link Term} containing the general assumptions.
    */
   protected Term buildFreePre(ProgramVariable selfVar,
                               KeYJavaType selfKJT,
                               ImmutableList<ProgramVariable> paramVars,
                               List<LocationVariable> heaps) {
      // "self != null"
      final Term selfNotNull = generateSelfNotNull(getProgramMethod(), selfVar);

      // "self.<created> = TRUE"
      final Term selfCreated = generateSelfCreated(heaps, getProgramMethod(), selfVar);

      // "MyClass::exactInstance(self) = TRUE"
      final Term selfExactType = generateSelfExactType(getProgramMethod(), selfVar, selfKJT);

      // conjunction of...
      // - "p_i.<created> = TRUE | p_i = null" for object parameters, and
      // - "inBounds(p_i)" for integer parameters
      Term paramsOK = generateParamsOK(paramVars);

      // initial value of measured_by clause
      final Term mbyAtPreDef = generateMbyAtPreDef(selfVar, paramVars);
      Term wellFormed = null;
      for (LocationVariable heap : heaps) {
         final Term wf = TB.wellFormed(TB.var(heap), services);
         if (wellFormed == null) {
            wellFormed = wf;
         }
         else {
            wellFormed = TB.and(wellFormed, wf);
         }
      }

      return TB.and(new Term[] { wellFormed != null ? wellFormed : TB.tt(), selfNotNull, selfCreated, selfExactType, paramsOK, mbyAtPreDef });
   }

   /**
    * Generates the general assumption that self is not null.
    * @param pm The {@link IProgramMethod} to execute.
    * @param selfVar The self variable.
    * @return The term representing the general assumption.
    */
   protected Term generateSelfNotNull(IProgramMethod pm, ProgramVariable selfVar) {
      return selfVar == null || pm.isConstructor() ?
             TB.tt() :
             TB.not(TB.equals(TB.var(selfVar), TB.NULL(services)));
   }

   /**
    * Generates the general assumption that self is created.
    * @param pm The {@link IProgramMethod} to execute.
    * @param selfVar The self variable.
    * @return The term representing the general assumption.
    */
   protected Term generateSelfCreated(List<LocationVariable> heaps, IProgramMethod pm, ProgramVariable selfVar) {
	  if(selfVar == null || pm.isConstructor()) {
		  return TB.tt();
	  }
	  Term created = null;
	  for(LocationVariable heap : heaps) {
		  if(heap == services.getTypeConverter().getHeapLDT().getSavedHeap())
			  continue;
		  final Term cr = TB.created(services, TB.var(heap), TB.var(selfVar));
		  if(created == null) {
			  created = cr;
		  }else{
			  created = TB.and(created, cr);
		  }
	  }
	  return created;
   }


   /**
    * Generates the general assumption which defines the type of self.
    * @param pm The {@link IProgramMethod} to execute.
    * @param selfVar The self variable.
    * @param selfKJT The {@link KeYJavaType} of the self variable.
    * @return The term representing the general assumption.
    */
   protected Term generateSelfExactType(IProgramMethod pm,
                                        ProgramVariable selfVar,
                                        KeYJavaType selfKJT) {
      final Term selfExactType = selfVar == null || pm.isConstructor() ?
            TB.tt() :
            TB.exactInstance(services, selfKJT.getSort(), TB.var(selfVar));
      return selfExactType;
   }

   /**
    * Generates the general assumption that all parameter arguments are valid.
    * @param paramVars The parameters {@link ProgramVariable}s.
    * @return The term representing the general assumption.
    */
   protected Term generateParamsOK(ImmutableList<ProgramVariable> paramVars) {
      Term paramsOK = TB.tt();
      for (ProgramVariable paramVar : paramVars) {
         paramsOK = TB.and(paramsOK, TB.reachableValue(services, paramVar));
      }
      return paramsOK;
   }

   protected abstract Term generateMbyAtPreDef(ProgramVariable selfVar,
                                               ImmutableList<ProgramVariable> paramVars);

   /**
    * Creates the precondition.
    * @param modHeaps The heaps.
    * @param selfVar The self variable.
    * @param paramVars The parameters {@link ProgramVariable}s.
    * @param atPreVars Mapping of {@link LocationVariable} to the {@link LocationVariable} which contains the initial value.
    * @param services The {@link Services} to use.
    * @return The {@link Term} representing the precondition.
    */
   protected abstract Term getPre(List<LocationVariable> modHeaps,
                                  ProgramVariable selfVar,
                                  ImmutableList<ProgramVariable> paramVars,
                                  Map<LocationVariable, LocationVariable> atPreVars,
                                  Services services);

   /**
    * Creates the postcondition.
    * @param modHeaps The heaps.
    * @param selfVar The self variable.
    * @param paramVars The parameters {@link ProgramVariable}s.
    * @param resultVar The result variable.
    * @param exceptionVar The exception variable.
    * @param atPreVars Mapping of {@link LocationVariable} to the {@link LocationVariable} which contains the initial value.
    * @param services The {@link Services} to use.
    * @return The {@link Term} representing the postcondition.
    */
   protected abstract Term getPost(List<LocationVariable> modHeaps,
                                   ProgramVariable selfVar,
                                   ImmutableList<ProgramVariable> paramVars,
                                   ProgramVariable resultVar,
                                   ProgramVariable exceptionVar,
                                   Map<LocationVariable, LocationVariable> atPreVars,
                                   Services services);

   protected abstract Term getGlobalDefs (LocationVariable heap, Term heapTerm, Term selfTerm, ImmutableList<Term> paramTerms, Services services);

   /**
    * Checks if an uninterpreted predicate is added to the postcondition or not.
    * @return {@code true} postcondition contains uninterpreted predicate, {@code false} uninterpreted predicate is not contained in postcondition.
    */
   public boolean isAddUninterpretedPredicate() {
      return addUninterpretedPredicate;
   }

   /**
    * Checks if the modality is labeled with the {@link SymbolicExecutionTermLabel}.
    * @return {@code true} modality is labled, {@code false} modality is not labled.
    */
   public boolean isAddSymbolicExecutionLabel() {
      return addSymbolicExecutionLabel;
   }

   /**
    * Returns the name used for the uninterpreted predicate.
    * @return The name of the uninterpreted predicate.
    */
   protected String getUninterpretedPredicateName() {
      return "SETAccumulate";
   }

   /**
    * Builds a {@link Term} to use in the postcondition of the generated
    * {@link Sequent} which represents the uninterpreted predicate.
    * @param paramVars The parameters {@link ProgramVariable}s.
    * @param exceptionVar The exception variable.
    * @param name The name of the uninterpreted predicate.
    * @return The created uninterpreted predicate.
    */
   protected Term buildUninterpretedPredicate(ImmutableList<ProgramVariable> paramVars,
                                              ProgramVariable exceptionVar,
                                              String name) {
      // Make sure that the predicate is not already created
      if (uninterpretedPredicate != null) {
         throw new IllegalStateException("The uninterpreted predicate is already available.");
      }
      // Create parameters for predicate SETAccumulate(HeapSort, MethodParameter1Sort, ... MethodParameterNSort)
      ImmutableList<Term> arguments = TB.var(paramVars); // Method parameters
      arguments = arguments.prepend(TB.var(exceptionVar)); // Exception variable (As second argument for the predicate)
      arguments = arguments.prepend(TB.getBaseHeap(services)); // Heap (As first argument for the predicate)
      // Create non-rigid predicate with signature: SETAccumulate(HeapSort, MethodParameter1Sort, ... MethodParameterNSort)
      ImmutableList<Sort> argumentSorts = TB.getSorts(arguments);
      Function f = new Function(new Name(TB.newName(services, name)),
                                Sort.FORMULA,
                                argumentSorts.toArray(new Sort[argumentSorts.size()]));
      services.getNamespaces().functions().addSafely(f);
      // Create term that uses the new predicate
      uninterpretedPredicate = TermBuilder.DF.func(f, arguments.toArray(new Term[arguments.size()]));
      return uninterpretedPredicate;
   }

   /**
    * Returns the used uninterpreted predicate.
    * @return The used uninterpreted predicate.
    */
   public Term getUninterpretedPredicate() {
      return uninterpretedPredicate;
   }

   /**
    * Builds the frame clause including the modifies clause.
    * @param modHeaps The heaps.
    * @param heapToAtPre The previous heap before execution.
    * @param selfVar The self variable.
    * @param paramVars The parameters {@link ProgramVariable}s.
    * @return The created {@link Term} representing the frame clause.
    */
   protected abstract Term buildFrameClause(List<LocationVariable> modHeaps,
                                            Map<LocationVariable,
                                            Map<Term, Term>> heapToAtPre,
                                            ProgramVariable selfVar,
                                            ImmutableList<ProgramVariable> paramVars);

   /**
    * Creates the {@link Term} which contains the modality including
    * the complete program to execute.
    * @param paramVars Formal parameters of method call.
    * @param formalParVars Arguments from formal parameters for method call.
    * @param selfVar The self variable.
    * @param resultVar The result variable.
    * @param exceptionVar The {@link ProgramVariable} used to store caught exceptions.
    * @param atPreVars Mapping of {@link LocationVariable} to the {@link LocationVariable} which contains the initial value.
    * @param postTerm The post condition.
    * @param sb The {@link StatementBlock} to execute in try block.
    * @return The created {@link Term}.
    */
   protected Term buildProgramTerm(ImmutableList<ProgramVariable> paramVars,
                                   ImmutableList<LocationVariable> formalParamVars,
                                   ProgramVariable selfVar,
                                   ProgramVariable resultVar,
                                   ProgramVariable exceptionVar,
                                   Map<LocationVariable, LocationVariable> atPreVars,
                                   Term postTerm,
                                   ImmutableList<StatementBlock> sb) {

      // create java block
      final JavaBlock jb = buildJavaBlock(formalParamVars, selfVar, resultVar, exceptionVar, atPreVars.keySet().contains(getSavedHeap()), sb);

      // create program term
      Term programTerm = TB.prog(getTerminationMarker(), jb, postTerm);

      // label modality if required
      if (addSymbolicExecutionLabel) {
         int labelID = services.getCounter(SymbolicExecutionTermLabel.PROOF_COUNTER_NAME).getCountPlusPlus();
         programTerm = TB.label(programTerm, new SymbolicExecutionTermLabel(labelID));
      }

      // create update
      Term update = buildUpdate(paramVars, formalParamVars, atPreVars);

      return TB.apply(update, programTerm, null);
   }

    /**
    * Returns the base heap.
    * @return The {@link LocationVariable} of the base heap.
    */
   protected LocationVariable getBaseHeap() {
      return services.getTypeConverter().getHeapLDT().getHeap();
   }

   /**
    * Returns the saved heap.
    * @return The {@link LocationVariable} of the saved heap.
    */
   protected LocationVariable getSavedHeap() {
      return services.getTypeConverter().getHeapLDT().getSavedHeap();
   }

   /**
    * Creates the try catch block to execute.
    * @param formalParVars Arguments from formal parameters for method call.
    * @param selfVar The self variable.
    * @param resultVar The result variable.
    * @param exceptionVar The {@link ProgramVariable} used to store caught exceptions.
    * @param transaction Transaction flag.
    * @param sb The {@link StatementBlock}s to execute.
    * @return The created {@link JavaBlock} which contains the try catch block.
    */
   protected JavaBlock buildJavaBlock(ImmutableList<LocationVariable> formalParVars,
                                      ProgramVariable selfVar,
                                      ProgramVariable resultVar,
                                      ProgramVariable exceptionVar,
                                      boolean transaction,
                                      ImmutableList<StatementBlock> sb) {
       assert sb.size() == 4 : "wrong number of blocks in method";
       final StatementBlock beforeTry = sb.head();
       final StatementBlock tryBlock = sb.tail().head();
       final StatementBlock catchBlock = sb.tail().tail().head();
       final StatementBlock finallyBlock = sb.tail().tail().tail().head();

      // create variables for try statement
      final KeYJavaType eType = javaInfo.getTypeByClassName("java.lang.Exception");
      final TypeReference excTypeRef = javaInfo.createTypeReference(eType);
      final ProgramElementName ePEN = new ProgramElementName("e");
      final ProgramVariable eVar = new LocationVariable(ePEN, eType);

      final StatementBlock sb2;
      if(exceptionVar == null) {
    	  sb2 = tryBlock;
      }else{
          // create try statement
          final CopyAssignment nullStat = new CopyAssignment(exceptionVar, NullLiteral.NULL);
          final VariableSpecification eSpec = new VariableSpecification(eVar);
          final ParameterDeclaration excDecl = new ParameterDeclaration(new Modifier[0], excTypeRef, eSpec, false);
          final CopyAssignment assignStat = new CopyAssignment(exceptionVar, eVar);
          final Catch catchStat = new Catch(excDecl,
                  catchBlock==null? new StatementBlock(assignStat): new StatementBlock(assignStat, catchBlock));
          final Branch[] branches = finallyBlock == null? new Branch[] {catchStat} : new Branch[] {catchStat,new Finally(finallyBlock)};
          final Try tryStat = new Try(tryBlock, branches);
          if (beforeTry == null)
              sb2 = new StatementBlock(transaction ?
                      new Statement[] {new TransactionStatement(de.uka.ilkd.key.java.recoderext.TransactionStatement.BEGIN),
                                                                nullStat,
                                                                tryStat,
                                                                new TransactionStatement(de.uka.ilkd.key.java.recoderext.TransactionStatement.FINISH) } :
                      new Statement[] {nullStat, tryStat});
          else
          sb2 = new StatementBlock(transaction ?
                                                    new Statement[] {new TransactionStatement(de.uka.ilkd.key.java.recoderext.TransactionStatement.BEGIN),
                                                                                              nullStat,
                                                                                              beforeTry,
                                                                                              tryStat,
                                                                                              new TransactionStatement(de.uka.ilkd.key.java.recoderext.TransactionStatement.FINISH) } :
                                                    new Statement[] {nullStat, beforeTry, tryStat});
      }
      // create java block
      JavaBlock result = JavaBlock.createJavaBlock(sb2);
      return result;
   }

   /**
    * Returns the {@link Modality} to use as termination marker.
    * @returnT he {@link Modality} to use as termination marker.
    */
   protected abstract Modality getTerminationMarker();

   /**
    * Builds the initial updates.
    * @param paramVars Formal parameters of method call.
    * @param formalParVars Arguments from formal parameters for method call.
    * @param atPreVars Mapping of {@link LocationVariable} to the {@link LocationVariable} which contains the initial value.
    * @return The {@link Term} representing the initial updates.
    */
   protected Term buildUpdate(ImmutableList<ProgramVariable> paramVars,
                              ImmutableList<LocationVariable> formalParamVars,
                              Map<LocationVariable, LocationVariable> atPreVars) {
      Term update = null;
      for(Entry<LocationVariable, LocationVariable> atPreEntry : atPreVars.entrySet()) {
         final Term u = TB.elementary(services, atPreEntry.getValue(), TB.getBaseHeap(services));
         if(update == null) {
            update = u;
         }else{
            update = TB.parallel(update, u);
         }
       }
       if (isCopyOfMethodArgumentsUsed()) {
          Iterator<LocationVariable> formalParamIt = formalParamVars.iterator();
          Iterator<ProgramVariable> paramIt = paramVars.iterator();
          while (formalParamIt.hasNext()) {
              Term paramUpdate = TB.elementary(services,
                                               formalParamIt.next(),
                                               TB.var(paramIt.next()));
              update = TB.parallel(update, paramUpdate);
          }
       }
       return update;
   }

   /**
    * Checks if a copy of the method call arguments are used instead
    * of the original method arguments.
    * @return {@code true} use copy of method call arguments, {@code false} use original method call arguments.
    */
   protected boolean isCopyOfMethodArgumentsUsed() {
      return true;
   }

   /**
    * Returns the name of the {@link Proof} based on the given transaction flag.
    * @param transactionFlag The transaction flag.
    * @return The proof name to use.
    */
   protected abstract String buildPOName(boolean transactionFlag);

   /**
    * {@inheritDoc}
    */
   @Override
   public void fillSaveProperties(Properties properties) throws IOException {
       super.fillSaveProperties(properties);
       if (isAddUninterpretedPredicate()) {
           properties.setProperty("addUninterpretedPredicate", isAddUninterpretedPredicate() + "");
       }
       if (isAddSymbolicExecutionLabel()) {
          properties.setProperty("addSymbolicExecutionLabel", isAddSymbolicExecutionLabel() + "");
       }
   }

   /**
    * Checks if the "addUninterpretedPredicate" value is set in the given {@link Properties}.
    * @param properties The {@link Properties} to read value from.
    * @return {@code true} is set, {@code false} is not set.
    */
   protected static boolean isAddUninterpretedPredicate(Properties properties) {
      String value = properties.getProperty("addUninterpretedPredicate");
      return value != null && !value.isEmpty() ? Boolean.valueOf(value) : false;
   }

   /**
    * Checks if the "addSymbolicExecutionLabel" value is set in the given {@link Properties}.
    * @param properties The {@link Properties} to read value from.
    * @return {@code true} is set, {@code false} is not set.
    */
   protected static boolean isAddSymbolicExecutionLabel(Properties properties) {
      String value = properties.getProperty("addSymbolicExecutionLabel");
      return value != null && !value.isEmpty() ? Boolean.valueOf(value) : false;
   }
}
