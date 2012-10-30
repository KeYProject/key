/*
 * To change this template, choose Tools | Templates and open the template in
 * the editor.
 */
package de.uka.ilkd.key.proof.init;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.Services;
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
import de.uka.ilkd.key.java.statement.*;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.proof.mgt.AxiomJustification;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.speclang.SymbolicExecData;
import java.util.Iterator;
import java.util.List;
import java.util.Map;



/**
 *
 * @author christoph
 */
public class SymbolicExecutionPO extends AbstractOperationPO implements ContractPO {

    private final ProofObligationVars vs;
    private final SymbolicExecData contract;
    protected Term mbyAtPre;


    public SymbolicExecutionPO(InitConfig initConfig,
                               SymbolicExecData contract) {
        super(initConfig, contract.getName());
        this.contract = contract;
        ProgramMethod pm = contract.getTarget();
        vs = new ProofObligationVars(pm, contract.getKJT(), services);
        assert (vs.self == null) == (pm.isStatic());
    }


    private Term buildPrecondition(final ProofObligationVars vs)
            throws ProofInputException {
        final Term freePre = buildFreePre(vs, contract.getKJT());
        final Term pre = contract.getPre(vs.heap, vs.self, vs.params, services);
        return TB.and(freePre, pre);
    }


    private Term buildSymbolicExecution(final ProofObligationVars vs) {
        ImmutableList<Term> posts = ImmutableSLList.<Term>nil();
        if (vs.selfAtPost != null) {
            posts = posts.append(TB.equals(vs.selfAtPost, vs.self));
        }
        if (vs.resultAtPost != null) {
            posts = posts.append(TB.equals(vs.resultAtPost, vs.result));
        }
        posts = posts.append(TB.equals(vs.exceptionAtPost, vs.exception));
        posts = posts.append(TB.equals(vs.heapAtPost, vs.heap));
        final Term prog = buildProgramTerm(vs, TB.and(posts));
        return prog;
    }


    /**
     * Builds the "general assumption". 
     * @throws ParserException 
     */
    private Term buildFreePre(ProofObligationVars vs,
                              KeYJavaType selfKJT)
            throws ProofInputException {

        // heap well formed
        final Term wellFormed = TB.wellFormed(vs.heap, services);
        
        // heap == heapAtPre
        final Term eqHeapAndHeapAtPre =
                TB.equals(vs.heap, vs.heapAtPre);

        //"self != null"
        final Term selfNotNull = generateSelfNotNull(contract.getTarget(), vs.self);

        //"self.<created> = TRUE"
        final Term selfCreated = generateSelfCreated(contract.getTarget(), vs.self);

        //"MyClass::exactInstance(self) = TRUE"
        final Term selfExactType =
                generateSelfExactType(contract.getTarget(), vs.self, selfKJT);

        //conjunction of... 
        //- "p_i.<created> = TRUE | p_i = null" for object parameters, and
        //- "inBounds(p_i)" for integer parameters
        Term paramsOK = generateParamsOK2(vs.params);

        //initial value of measured_by clause
        final Term mbyAtPreDef = generateMbyAtPreDef(vs.self, vs.params);

        return TB.and(wellFormed,
                        eqHeapAndHeapAtPre,
                        selfNotNull,
                        selfCreated,
                        selfExactType,
                        paramsOK,
                        mbyAtPreDef);
    }


    private JavaBlock buildJavaBlock(
            ImmutableList<LocationVariable> formalParVars,
            ProgramVariable selfVar,
            ProgramVariable resultVar,
            ProgramVariable exceptionVar) {
        //create method call
        final ImmutableArray<Expression> formalArray =
                new ImmutableArray<Expression>(formalParVars.toArray(
                new ProgramVariable[formalParVars.size()]));
        final StatementBlock sb;
        if (getContract().getTarget().isConstructor()) {
            assert selfVar != null;
            assert resultVar == null;
            final Expression[] formalArray2 =
                    formalArray.toArray(new Expression[formalArray.size()]);
            final New n =
                    new New(formalArray2, new TypeRef(getContract().getKJT()),
                            null);
            final CopyAssignment ca = new CopyAssignment(selfVar, n);
            sb = new StatementBlock(ca);
        } else {
            final MethodBodyStatement call =
                    new MethodBodyStatement(getContract().getTarget(), selfVar,
                                            resultVar, formalArray);
            sb = new StatementBlock(call);
        }

        //create variables for try statement
        final KeYJavaType eType =
                javaInfo.getTypeByClassName("java.lang.Exception");
        final TypeReference excTypeRef = javaInfo.createTypeReference(eType);
        final ProgramElementName ePEN = new ProgramElementName("e");
        final ProgramVariable eVar = new LocationVariable(ePEN, eType);

        //create try statement
        final CopyAssignment nullStat =
                new CopyAssignment(exceptionVar, NullLiteral.NULL);
        final VariableSpecification eSpec = new VariableSpecification(eVar);
        final ParameterDeclaration excDecl =
                new ParameterDeclaration(new Modifier[0], excTypeRef, eSpec,
                                         false);
        final CopyAssignment assignStat =
                new CopyAssignment(exceptionVar, eVar);
        final Catch catchStat =
                new Catch(excDecl, new StatementBlock(assignStat));
        final Try tryStat = new Try(sb, new Branch[]{catchStat});
        final StatementBlock sb2 = new StatementBlock(
                new Statement[]{nullStat, tryStat});

        //create java block
        JavaBlock result = JavaBlock.createJavaBlock(sb2);

        return result;
    }


    // Must be protected because it is overwritten in sub classes.
    protected Term buildProgramTerm(ProofObligationVars vs,
                                  Term postTerm) {
        //create formal parameters
        ImmutableList<LocationVariable> formalParamVars =
                ImmutableSLList.<LocationVariable>nil();
        for (Term param : vs.params) {
            ProgramVariable paramVar = param.op(ProgramVariable.class);
            ProgramElementName pen = new ProgramElementName("_"
                                                            + paramVar.name());
            LocationVariable formalParamVar =
                    new LocationVariable(pen, paramVar.getKeYJavaType());
            formalParamVars = formalParamVars.append(formalParamVar);
            register(formalParamVar);
        }

        //create java block
        final JavaBlock jb = buildJavaBlock(formalParamVars,
                                            vs.self != null
                                                ? vs.self.op(ProgramVariable.class)
                                                : null,
                                            vs.result != null
                                                ? vs.result.op(ProgramVariable.class)
                                                : null,
                                            vs.exception != null
                                                ? vs.exception.op(ProgramVariable.class)
                                                : null);

        //create program term
        final Modality symbExecMod;
        if (getContract().getModality() == Modality.BOX) {
            symbExecMod = Modality.DIA;
        } else if (getContract().getModality() == Modality.DIA) {
            symbExecMod = Modality.BOX;
        } else if (getContract().getModality() == Modality.BOX_TRANSACTION) {
            symbExecMod = Modality.DIA_TRANSACTION;
        } else {
            symbExecMod = Modality.BOX_TRANSACTION;
        }       
        final Term programTerm = TB.prog(symbExecMod, jb, postTerm);

        //create update
        Term update = TB.skip();
        Iterator<LocationVariable> formalParamIt = formalParamVars.iterator();
        Iterator<Term> paramIt = vs.params.iterator();
        while (formalParamIt.hasNext()) {
            Term paramUpdate = TB.elementary(services,
                                             formalParamIt.next(),
                                             paramIt.next());
            update = TB.parallel(update, paramUpdate);
        }

        return TB.apply(update, programTerm);
    }


    @Override
    public void readProblem()
            throws ProofInputException {
        Term pre = buildPrecondition(vs);
        Term symExec = buildSymbolicExecution(vs);

        assignPOTerms(TB.not(TB.and(pre, symExec)));
        collectClassAxioms(contract.getKJT());
    }


    @Override
    public boolean implies(ProofOblInput po) {
        if (!(po instanceof SymbolicExecutionPO)) {
            return false;
        }
        SymbolicExecutionPO cPO = (SymbolicExecutionPO) po;
        return contract.equals(cPO.contract);
    }


    @Override
    public SymbolicExecData getContract() {
        return (SymbolicExecData) contract;
    }


    @Override
    public Term getMbyAtPre() {
        return mbyAtPre;
    }


    protected void register(Taclet axiomTaclet) {
        assert axiomTaclet != null : "Proof obligation generation generated null taclet.";
        taclets = taclets.add(NoPosTacletApp.createNoPosTacletApp(axiomTaclet));
        initConfig.getProofEnv().registerRule(axiomTaclet,
                                              AxiomJustification.INSTANCE);
    }


    ProofObligationVars getProofObligationVariables() {
        return vs;
    }

    
    /**
     * {@inheritDoc}
     */
    @Override
    protected String buildPOName(boolean transactionFlag) {
       return getContract().getName();
    }

    
    /**
     * {@inheritDoc}
     */
    @Override
    protected IProgramMethod getProgramMethod() {
        return contract.getTarget();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    protected boolean isTransactionApplicable() {
        return false;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    protected KeYJavaType getCalleeKeYJavaType() {
        return contract.getKJT();
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
    protected Term generateMbyAtPreDef(Term selfVar,
                                       ImmutableList<Term> paramVars) {
        final Term mbyAtPreDef;
        if (contract.hasMby()) {
            final Function mbyAtPreFunc =
                    new Function(new Name(TB.newName(services, "mbyAtPre")),
                                 services.getTypeConverter().getIntegerLDT().targetSort());
            register(mbyAtPreFunc);
            mbyAtPre = TB.func(mbyAtPreFunc);
            final Term mby = contract.getMby(TB.getBaseHeap(services), selfVar, paramVars, services);
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
       return TB.tt();
    }
    
    /**
     * {@inheritDoc}
     */
    @Override
    protected Term buildFrameClause(List<LocationVariable> modHeaps,
                                    Map<LocationVariable, Map<Term, Term>> heapToAtPre,
                                    ProgramVariable selfVar,
                                    ImmutableList<ProgramVariable> paramVars) {
       return TB.tt();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    protected Modality getTerminationMarker() {
       return getContract().getModality();
    }

}
