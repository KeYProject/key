// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.proof.init;

import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.Iterator;
import java.util.Map;
import java.util.List;

import de.uka.ilkd.key.collection.*;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.Modifier;
import de.uka.ilkd.key.java.declaration.ParameterDeclaration;
import de.uka.ilkd.key.java.declaration.VariableSpecification;
import de.uka.ilkd.key.java.expression.literal.NullLiteral;
import de.uka.ilkd.key.java.expression.operator.CopyAssignment;
import de.uka.ilkd.key.java.expression.operator.New;
import de.uka.ilkd.key.java.reference.TypeRef;
import de.uka.ilkd.key.java.reference.TypeReference;
import de.uka.ilkd.key.java.statement.Branch;
import de.uka.ilkd.key.java.statement.Catch;
import de.uka.ilkd.key.java.statement.TransactionStatement;
import de.uka.ilkd.key.java.statement.MethodBodyStatement;
import de.uka.ilkd.key.java.statement.Try;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;
import de.uka.ilkd.key.speclang.HeapContext;



/**
 * The proof obligation for operation contracts. 
 */
// The class can not be final, it is required in the symbolic execution debugger to modify the behavior in it 
public class FunctionalOperationContractPO
        extends AbstOpContractPO {

    public FunctionalOperationContractPO(InitConfig initConfig,
                                         FunctionalOperationContract contract) {
        super(initConfig, contract.getName(), contract);
    }


    //-------------------------------------------------------------------------
    //internal methods
    //-------------------------------------------------------------------------    
    /**
     * Builds the "general assumption". 
     */
    private Term buildFreePre(ProgramVariable selfVar,
                              KeYJavaType selfKJT,
                              ImmutableList<ProgramVariable> paramVars)
            throws ProofInputException {
        //"self != null"
        final Term selfNotNull = generateSelfNotNull(selfVar);

        //"self.<created> = TRUE"
        final Term selfCreated = generateSelfCreated(selfVar);

        //"MyClass::exactInstance(self) = TRUE"
        final Term selfExactType = generateSelfExactType(selfVar, selfKJT);

        //conjunction of... 
        //- "p_i.<created> = TRUE | p_i = null" for object parameters, and
        //- "inBounds(p_i)" for integer parameters
        Term paramsOK = generateParamsOK(paramVars);

        //initial value of measured_by clause
        final Term mbyAtPreDef = generateMbyAtPreDef(selfVar, paramVars);

        if(getContract().transactionContract()) {
          return TB.and(new Term[]{TB.wellFormed(getBaseHeap(), services), 
                                   TB.wellFormed(getSavedHeap(), services),
                                   selfNotNull,
                                   selfCreated,
                                   selfExactType,
                                   paramsOK,
                                   mbyAtPreDef});
        }else{
          return TB.and(new Term[]{TB.wellFormed(getBaseHeap(), services), 
                                   selfNotNull,
                                   selfCreated,
                                   selfExactType,
                                   paramsOK,
                                   mbyAtPreDef});
        }
    }


    private JavaBlock buildJavaBlock(
            ImmutableList<LocationVariable> formalParVars,
            ProgramVariable selfVar,
            ProgramVariable resultVar,
            ProgramVariable exceptionVar) {
        //create method call
        final ImmutableArray<Expression> formalArray = new ImmutableArray<Expression>(formalParVars.toArray(
                new ProgramVariable[formalParVars.size()]));
        final StatementBlock sb;
        if (getContract().getTarget().isConstructor()) {
            assert selfVar != null;
            assert resultVar == null;
            final Expression[] formalArray2 = formalArray.toArray(
                    new Expression[formalArray.size()]);
            final New n = new New(formalArray2, new TypeRef(
                    getContract().getKJT()), null);
            final CopyAssignment ca = new CopyAssignment(selfVar, n);
            sb = new StatementBlock(ca);
        } else {
            final MethodBodyStatement call =
                    new MethodBodyStatement(getContract().getTarget(),
                                            selfVar,
                                            resultVar,
                                            formalArray);
            sb = new StatementBlock(call);
        }

        //create variables for try statement
        final KeYJavaType eType = javaInfo.getTypeByClassName(
                "java.lang.Exception");
        final TypeReference excTypeRef = javaInfo.createTypeReference(eType);
        final ProgramElementName ePEN = new ProgramElementName("e");
        final ProgramVariable eVar = new LocationVariable(ePEN, eType);

        //create try statement
        final CopyAssignment nullStat = new CopyAssignment(exceptionVar,
                                                           NullLiteral.NULL);
        final VariableSpecification eSpec = new VariableSpecification(eVar);
        final ParameterDeclaration excDecl = new ParameterDeclaration(
                new Modifier[0],
                                                                      excTypeRef,
                                                                      eSpec,
                                                                      false);
        final CopyAssignment assignStat = new CopyAssignment(exceptionVar, eVar);
        final Catch catchStat = new Catch(excDecl,
                                          new StatementBlock(assignStat));
        final Try tryStat = new Try(sb, new Branch[]{catchStat});
        final StatementBlock sb2 = new StatementBlock(
           getContract().transactionContract() ? 
                new Statement[]{
                        new TransactionStatement(de.uka.ilkd.key.java.recoderext.TransactionStatement.BEGIN),
                        nullStat, tryStat,
                        new TransactionStatement(de.uka.ilkd.key.java.recoderext.TransactionStatement.FINISH)}
              :
                new Statement[]{nullStat, tryStat});

        //create java block
        JavaBlock result = JavaBlock.createJavaBlock(sb2);

        return result;
    }

    // Must be protected because it is overwritten in sub classes.
    protected Term buildProgramTerm(ImmutableList<ProgramVariable> paramVars,
                                    ProgramVariable selfVar,
                                    ProgramVariable resultVar,
                                    ProgramVariable exceptionVar,
                                    Map<LocationVariable,LocationVariable> atPreVars,
                                    Term postTerm) {
        //create formal parameters
        ImmutableList<LocationVariable> formalParamVars =
                ImmutableSLList.<LocationVariable>nil();
        for (ProgramVariable paramVar : paramVars) {
            ProgramElementName pen = new ProgramElementName("_"
                                                            + paramVar.name());
            LocationVariable formalParamVar =
                    new LocationVariable(pen, paramVar.getKeYJavaType());
            formalParamVars = formalParamVars.append(formalParamVar);
            register(formalParamVar);
        }

        //create java block
        final JavaBlock jb = buildJavaBlock(formalParamVars,
                                            selfVar,
                                            resultVar,
                                            exceptionVar);

        //create program term
        final Term programTerm = TB.prog(getContract().getPOModality(), jb,
                                         postTerm);

        //create update
        Term update = null;
        for(LocationVariable heap : atPreVars.keySet()) {
          final Term u = TB.elementary(services, atPreVars.get(heap), TB.getBaseHeap(services));
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

        return TB.apply(update, programTerm);
    }
    
    private LocationVariable getBaseHeap() {
        return services.getTypeConverter().getHeapLDT().getHeap();
    }


    //-------------------------------------------------------------------------
    //public interface
    //-------------------------------------------------------------------------        
    @Override
    public void readProblem()
            throws ProofInputException {
        final ProgramMethod pm = getContract().getTarget();
        final HeapContext hc = getContract().getHeapContext();

        //prepare variables, program method, heapAtPre
        final ImmutableList<ProgramVariable> paramVars = TB.paramVars(services,
                                                                      pm, true);
        final ProgramVariable selfVar = TB.selfVar(services, pm,
                                                   contract.getKJT(), true);
        final ProgramVariable resultVar = TB.resultVar(services, pm, true);
        final ProgramVariable exceptionVar = TB.excVar(services, pm, true);
       
        final Map<LocationVariable,LocationVariable> atPreVars = hc.getBeforeAtPreVars(services, "AtPre");

        final List<LocationVariable> modHeaps = hc.getModHeaps(services);
        final Map<LocationVariable,Map<Term,Term>> heapToAtPre = new LinkedHashMap<LocationVariable,Map<Term,Term>>();
        
        for(LocationVariable heap : modHeaps) {
           heapToAtPre.put(heap, new HashMap<Term, Term>());
           heapToAtPre.get(heap).put(TB.var(heap), TB.var(atPreVars.get(heap)));
        }

        // FIXME check this again!?
        if(modHeaps.contains(getSavedHeap())) {
           heapToAtPre.get(getSavedHeap()).put(TB.getBaseHeap(services), TB.var(atPreVars.get(getSavedHeap())));
        }

        //register the variables so they are declared in proof header 
        //if the proof is saved to a file
        register(paramVars);
        register(selfVar);
        register(resultVar);
        register(exceptionVar);
        for(LocationVariable lv : atPreVars.values()) {
          register(lv);
        }

        //build precondition
        final Term pre = TB.and(buildFreePre(selfVar,
                                             contract.getKJT(),
                                             paramVars),
                                contract.getPre(selfVar, paramVars, atPreVars, services));

        //build program term
        final Term postTerm = getContract().getPost(selfVar,
                                                    paramVars,
                                                    resultVar,
                                                    exceptionVar,
                                                    atPreVars,
                                                    services);
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
        
        
        final Term post = TB.and(postTerm, frameTerm);
        final Term progPost = buildProgramTerm(paramVars,
                                               selfVar,
                                               resultVar,
                                               exceptionVar,
                                               atPreVars,
                                               post);

        //save in field
        assignPOTerms(TB.imp(pre, progPost));

        //add axioms
        collectClassAxioms(contract.getKJT());
        hc.reset();
    }


    private LocationVariable getSavedHeap() {
        return services.getTypeConverter().getHeapLDT().getSavedHeap();
    }


    @Override
    public boolean implies(ProofOblInput po) {
        if (!(po instanceof FunctionalOperationContractPO)) {
            return false;
        }
        AbstOpContractPO cPO = (AbstOpContractPO) po;
        return specRepos.splitContract(cPO.contract).subset(specRepos.splitContract(
                contract));
    }


    @Override
    public FunctionalOperationContract getContract() {
        return (FunctionalOperationContract) contract;
    }


    @Override
    public Term getMbyAtPre() {
        return mbyAtPre;
    }


    @Override
    public boolean equals(Object o) {
        if (!(o instanceof FunctionalOperationContractPO)) {
            return false;
        } else {
            return contract.equals(((AbstOpContractPO) o).contract);
        }
    }


    @Override
    public int hashCode() {
        return contract.hashCode();
    }


    protected Term generateSelfNotNull(ProgramVariable selfVar) {
        return selfVar == null || getContract().getTarget().isConstructor()
               ? TB.tt()
               : TB.not(TB.equals(TB.var(selfVar), TB.NULL(services)));
    }


    protected Term generateSelfCreated(ProgramVariable selfVar) {
        return selfVar == null || getContract().getTarget().isConstructor()
               ? TB.tt()
               : TB.created(services, TB.var(selfVar));
    }


    protected Term generateSelfExactType(ProgramVariable selfVar,
                                         KeYJavaType selfKJT) {
        final Term selfExactType = selfVar == null
                                   || getContract().getTarget().isConstructor()
                                   ? TB.tt()
                                   : TB.exactInstance(services,
                                                      selfKJT.getSort(),
                                                      TB.var(selfVar));
        return selfExactType;
    }


    protected Term generateParamsOK(ImmutableList<ProgramVariable> paramVars) {
        Term paramsOK = TB.tt();
        for (ProgramVariable paramVar : paramVars) {
            paramsOK = TB.and(paramsOK, TB.reachableValue(services, paramVar));
        }
        return paramsOK;
    }


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
}
