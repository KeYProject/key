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
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Properties;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.expression.operator.CopyAssignment;
import de.uka.ilkd.key.java.expression.operator.New;
import de.uka.ilkd.key.java.reference.TypeRef;
import de.uka.ilkd.key.java.statement.MethodBodyStatement;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SymbolicExecutionTermLabel;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;

/**
 * <p>
 * The proof obligation for operation contracts.
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
 * exc=null;try {&lt;methodBodyExpand&gt;}catch(java.lang.Exception e) {exc = e}
 * &lt;modalityEnd&gt;
 * (exc = null & &lt;postconditions &gt; & &lt;optionalUninterpretedPredicate&gt;)
 * </code>
 * </pre>
 * </p>
 */
public class FunctionalOperationContractPO extends AbstractOperationPO implements ContractPO {
    public static Map<Boolean,String> TRANSACTION_TAGS = new LinkedHashMap<Boolean,String>();

    private FunctionalOperationContract contract;

    protected Term mbyAtPre;

    static {
      TRANSACTION_TAGS.put(false, "transaction_inactive");
      TRANSACTION_TAGS.put(true, "transaction_active");
    }

    /**
     * Constructor.
     * @param initConfig The {@link InitConfig} to use.
     * @param contract The {@link FunctionalOperationContractPO} to prove.
     */
    public FunctionalOperationContractPO(InitConfig initConfig,
                                         FunctionalOperationContract contract) {
        super(initConfig, contract.getName());
        this.contract = contract;
    }

    /**
     * Constructor.
     * @param initConfig The {@link InitConfig} to use.
     * @param contract The {@link FunctionalOperationContractPO} to prove.
     * @param addUninterpretedPredicate {@code true} postcondition contains uninterpreted predicate, {@code false} uninterpreted predicate is not contained in postcondition.
    * @param addSymbolicExecutionLabel {@code true} to add the {@link SymbolicExecutionTermLabel} to the modality, {@code false} to not label the modality.
     */
    public FunctionalOperationContractPO(InitConfig initConfig,
                                         FunctionalOperationContract contract,
                                         boolean addUninterpretedPredicate,
                                         boolean addSymbolicExecutionLabel) {
        super(initConfig, contract.getName(), addUninterpretedPredicate, addSymbolicExecutionLabel);
        this.contract = contract;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    protected IProgramMethod getProgramMethod() {
       return getContract().getTarget();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    protected boolean isTransactionApplicable() {
       return getContract().transactionApplicableContract();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    protected KeYJavaType getCalleeKeYJavaType() {
       return getContract().getKJT();
    }
    
    /**
     * {@inheritDoc}
     */
    @Override
    protected StatementBlock buildOperationBlock(ImmutableList<LocationVariable> formalParVars,
                                                 ProgramVariable selfVar,
                                                 ProgramVariable resultVar) {
       final ImmutableArray<Expression> formalArray = new ImmutableArray<Expression>(formalParVars.toArray(
             new ProgramVariable[formalParVars.size()]));

       if (getContract().getTarget().isConstructor()) {
            assert selfVar != null;
            assert resultVar == null;
            final Expression[] formalArray2 = formalArray.toArray(
                    new Expression[formalArray.size()]);
            final New n = new New(formalArray2, new TypeRef(
                    getContract().getKJT()), null);
            final CopyAssignment ca = new CopyAssignment(selfVar, n);
            return new StatementBlock(ca);
        } else {
            final MethodBodyStatement call =
                    new MethodBodyStatement(getContract().getTarget(),
                                            selfVar,
                                            resultVar,
                                            formalArray);
            return new StatementBlock(call);
        }
    }
    
    /**
     * {@inheritDoc}
     */
    @Override
    protected Term generateMbyAtPreDef(ProgramVariable selfVar,
                                       ImmutableList<ProgramVariable> paramVars) {
        final Term mbyAtPreDef;
        if (contract.hasMby()) {
            final Function mbyAtPreFunc =
                    new Function(new Name(TB.newName(services, "mbyAtPre")),
                                 services.getTypeConverter().getIntegerLDT().targetSort());
            register(mbyAtPreFunc);
            mbyAtPre = TB.func(mbyAtPreFunc);
            final Term mby = contract.getMby(selfVar, paramVars, services);
            mbyAtPreDef = TB.equals(mbyAtPre, mby);
        } else {
            mbyAtPreDef = TB.tt();
        }
        return mbyAtPreDef;
    }
    
    /**
     * {@inheritDoc}
     */
    @Override
    protected Term getPre(List<LocationVariable> modHeaps,
                          ProgramVariable selfVar, 
                          ImmutableList<ProgramVariable> paramVars,
                          Map<LocationVariable, LocationVariable> atPreVars, 
                          Services services) {
       return contract.getPre(modHeaps, selfVar, paramVars, atPreVars, services);
    }
    
    /**
     * {@inheritDoc}
     */
    @Override
    protected Term getPost(List<LocationVariable> modHeaps, 
                           ProgramVariable selfVar, ImmutableList<ProgramVariable> paramVars, 
                           ProgramVariable resultVar, 
                           ProgramVariable exceptionVar, 
                           Map<LocationVariable, LocationVariable> atPreVars, 
                           Services services) {
       return contract.getPost(modHeaps, selfVar, paramVars, resultVar, exceptionVar, atPreVars, services);
    }
    
    /**
     * {@inheritDoc}
     */
    @Override
    protected Term buildFrameClause(List<LocationVariable> modHeaps,
                                    Map<LocationVariable, Map<Term, Term>> heapToAtPre,
                                    ProgramVariable selfVar, 
                                    ImmutableList<ProgramVariable> paramVars) {
       Term frameTerm = null;
       for(LocationVariable heap : modHeaps) {
          final Term ft;
          if(!getContract().hasModifiesClause() && heap == getBaseHeap()) {
            // strictly pure have a different contract.
            ft = TB.frameStrictlyEmpty(services, TB.var(heap), heapToAtPre.get(heap));
          }else{
            ft = TB.frame(services, TB.var(heap),
                 heapToAtPre.get(heap), getContract().getMod(heap, selfVar,
                         paramVars, services));
          }
          if(frameTerm == null) {
            frameTerm = ft;
          }else{
            frameTerm = TB.and(frameTerm, ft);
          }
       }
       return frameTerm;
    }
    
    /**
     * Returns the base heap.
     * @return The {@link LocationVariable} which contains the base heap.
     */
    private LocationVariable getBaseHeap() {
       return services.getTypeConverter().getHeapLDT().getHeap();
    }
    
    /**
     * {@inheritDoc}
     */
    @Override
    protected Modality getTerminationMarker() {
       return getContract().getModality();
    }
    
    /**
     * {@inheritDoc}
     */
    @Override
    protected Term buildUpdate(ImmutableList<ProgramVariable> paramVars,
                               ImmutableList<LocationVariable> formalParamVars,
                               Map<LocationVariable,LocationVariable> atPreVars) {
       Term update = null;
       for(LocationVariable heap : atPreVars.keySet()) {
          final Term u = TB.elementary(services, atPreVars.get(heap), heap == getSavedHeap() ? TB.getBaseHeap(services) : TB.var(heap));
          if(update == null) {
             update = u;
          }else{
             update = TB.parallel(update, u);
          }
        }
        Iterator<LocationVariable> formalParamIt = formalParamVars.iterator();
        Iterator<ProgramVariable> paramIt = paramVars.iterator();
        while (formalParamIt.hasNext()) {
            Term paramUpdate = TB.elementary(services,
                                             formalParamIt.next(),
                                             TB.var(paramIt.next()));
            update = TB.parallel(update, paramUpdate);
        }
        return update;
    }
    
    /**
     * {@inheritDoc}
     */
    @Override
    protected String buildPOName(boolean transactionFlag) {
       return getContract().getName()+"."+TRANSACTION_TAGS.get(transactionFlag);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public FunctionalOperationContract getContract() {
        return contract;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Term getMbyAtPre() {
        return mbyAtPre;
    }
    
    /**
     * {@inheritDoc}
     */
    @Override
    public boolean implies(ProofOblInput po) {
        if (!(po instanceof FunctionalOperationContractPO)) {
            return false;
        }
        FunctionalOperationContractPO cPO = (FunctionalOperationContractPO) po;
        return specRepos.splitContract(cPO.contract).subset(specRepos.splitContract(contract));
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean equals(Object o) {
       if (o instanceof FunctionalOperationContractPO) {
          return contract.equals(((FunctionalOperationContractPO)o).contract);
       }
       return false;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public int hashCode() {
        return contract.hashCode();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void fillSaveProperties(Properties properties) throws IOException {
        super.fillSaveProperties(properties);
        properties.setProperty("contract", contract.getName());
    }
    
    /**
     * Instantiates a new proof obligation with the given settings.
     * @param initConfig The already load {@link InitConfig}.
     * @param properties The settings of the proof obligation to instantiate.
     * @return The instantiated proof obligation.
     * @throws IOException Occurred Exception.
     */
    public static LoadedPOContainer loadFrom(InitConfig initConfig, Properties properties) throws IOException {
       String contractName = properties.getProperty("contract");
       int proofNum = 0;
       String baseContractName = null;
       int ind = -1;
       for (String tag : FunctionalOperationContractPO.TRANSACTION_TAGS.values()) {
          ind = contractName.indexOf("." + tag);
          if (ind > 0) {
             break;
          }
          proofNum++;
       }
       if (ind == -1) {
          baseContractName = contractName;
          proofNum = 0;
       }
       else {
          baseContractName = contractName.substring(0, ind);
       }
       final Contract contract = initConfig.getServices().getSpecificationRepository().getContractByName(baseContractName);
       if (contract == null) {
          throw new RuntimeException("Contract not found: " + baseContractName);
       }
       else {
          ProofOblInput po;
          if (isAddUninterpretedPredicate(properties)) {
             if (!(contract instanceof FunctionalOperationContract)) {
                throw new IOException("Found contract \"" + contract + "\" is no FunctionalOperationContract.");
             }
             po = new FunctionalOperationContractPO(initConfig, (FunctionalOperationContract)contract, true, true);
          }
          else {
             po = contract.createProofObl(initConfig, contract);
          }
          return new LoadedPOContainer(po, proofNum);
       }
    }
}
