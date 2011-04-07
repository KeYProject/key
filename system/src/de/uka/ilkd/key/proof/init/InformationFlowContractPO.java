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
import de.uka.ilkd.key.java.statement.MethodBodyStatement;
import de.uka.ilkd.key.java.statement.Try;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.parser.ParserException;
import de.uka.ilkd.key.speclang.InformationFlowContract;
import de.uka.ilkd.key.util.LinkedHashMap;
import java.util.Iterator;



/**
 * The proof obligation for dependency contracts. 
 */
public final class InformationFlowContractPO extends AbstOpContractPO {

    public InformationFlowContractPO(
            InitConfig initConfig,
            InformationFlowContract contract) {
        super(initConfig, contract.getName(), contract);
    }

    //-------------------------------------------------------------------------
    //internal methods
    //-------------------------------------------------------------------------    

    /**
     * Builds the "general assumption". 
     * @throws ParserException 
     */
    private Term buildFreePre(
            ProofObligationVariables vs,
            KeYJavaType selfKJT,
            Term updateHeapAtPre1,
            Term updateHeapAtPre2)
            throws ProofInputException, ParserException {

        final Term simpleFreePre =
                TB.parseTerm(
                "  wellFormed(heapAtPre1)"
                + "& wellFormed(heapAtPre2)"
                + "& self != null"
                + "& { heap := heapAtPre1 }"
                + "  self.<created> = TRUE"
                + "& { heap := heapAtPre2 }"
                + "  self.<created> = TRUE",
                services);

        //"MyClass::exactInstance(self) = TRUE"
        final Term selfExactType = generateSelfExactType(vs.selfVar, selfKJT);

        //conjunction of... 
        //- "p_i.<created> = TRUE | p_i = null" for object parameters, and
        //- "inBounds(p_i)" for integer parameters
        Term paramsOK1 =
                TB.apply(updateHeapAtPre1, generateParamsOK(vs.paramVars1));
        Term paramsOK2 =
                TB.apply(updateHeapAtPre2, generateParamsOK(vs.paramVars2));

        //initial value of measured_by clause
        final Term mbyAtPreDef1 =
                TB.apply(
                updateHeapAtPre1,
                generateMbyAtPreDef(vs.selfVar, vs.paramVars1));
        final Term mbyAtPreDef2 =
                TB.apply(
                updateHeapAtPre2,
                generateMbyAtPreDef(vs.selfVar, vs.paramVars2));

        return TB.and(
                simpleFreePre,
                TB.apply(updateHeapAtPre1, selfExactType),
                TB.apply(updateHeapAtPre2, selfExactType),
                paramsOK1,
                paramsOK2,
                mbyAtPreDef1,
                mbyAtPreDef2);
    }


    private Term buildInputOutputRelations(ProofObligationVariables vs)
            throws ParserException {
        final ImmutableList<ImmutableList<Term>> secureFors =
                getContract().getSecureFors(vs.selfVar, vs.paramVars1, services);
        ImmutableList<Term> inputOutputRelations =
                ImmutableSLList.<Term>nil();
        for (ImmutableList<Term> secureFor : secureFors) {
            assert secureFor.size() == vs.paramVars1.size() + 1;
            final Term resultLocSet = secureFor.head();
            Term inputOutputRelation =
                    buildInputOutputRelation(resultLocSet, secureFor, vs);
            inputOutputRelations = inputOutputRelations.append(
                    inputOutputRelation);
        }
        return TB.and(inputOutputRelations);
    }


    private Term buildInputOutputRelation(Term referenceLocSet,
                                          ImmutableList<Term> secureFor,
                                          ProofObligationVariables vs)
            throws ParserException {
        // LocSets of the parameters without the result LocSet
        final ImmutableList<Term> paramLocSets = secureFor.tail();

        final ImmutableList<Term> inputRelations =
                buildEqualsRelations(referenceLocSet, paramLocSets,
                                     vs.paramVars1.iterator(),
                                     vs.paramVars2.iterator(),
                                     TB.var(vs.heapAtPreVar1),
                                     TB.var(vs.heapAtPreVar2));
        final ImmutableList<Term> outputRelations =
                buildEqualsRelations(referenceLocSet, secureFor,
                                     vs.paramVars1.prepend(vs.resultVar1).iterator(),
                                     vs.paramVars2.prepend(vs.resultVar2).iterator(),
                                     TB.var(vs.heapAtPostVar1),
                                     TB.var(vs.heapAtPostVar2));
        return TB.imp(TB.and(inputRelations), TB.and(outputRelations));
    }


    private ImmutableList<Term> buildEqualsRelations(Term referenceLocSet,
                                                     ImmutableList<Term> paramLocSets,
                                                     Iterator<ProgramVariable> paramVars1It,
                                                     Iterator<ProgramVariable> paramVars2It,
                                                     Term heap1,
                                                     Term heap2)
            throws ParserException {
        ImmutableList<Term> inputRelations = ImmutableSLList.<Term>nil();
        for (Term paramLocSet : paramLocSets) {
            inputRelations =
                    inputRelations.append(
                    buildParamEqualsRelation(referenceLocSet,
                                             paramLocSet,
                                             paramVars1It.next(),
                                             paramVars2It.next(),
                                             heap1,
                                             heap2));
        }
        inputRelations =
                inputRelations.append(buildMainEqualsRelation(referenceLocSet));
        return inputRelations;
    }


    private Term buildMainEqualsRelation(Term referenceLocSet)
            throws ParserException {
        return TB.parseTerm("equalsAtLocs(heapAtPre1, heapAtPre2, "
                            + referenceLocSet + ", " + referenceLocSet + ")",
                            services);
    }


    private Term buildParamEqualsRelation(Term referenceLocSet,
                                          Term paramLocSet,
                                          ProgramVariable paramVar1,
                                          ProgramVariable paramVar2,
                                          Term heap1,
                                          Term heap2)
            throws ParserException {
        final Term param1 = TB.var(paramVar1);
        final Term param2 = TB.var(paramVar2);
        return TB.parseTerm("    subset(" + paramLocSet + ", " + referenceLocSet
                            + ")"
                            + " -> equals(" + heap1 + ", " + param1 + ", "
                            + "           " + heap2 + ", " + param2 + ")",
                            services);
    }


    private JavaBlock buildJavaBlock(
            ImmutableList<ProgramVariable> formalParVars,
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
                    new New(formalArray2, new TypeRef(contract.getKJT()), null);
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
        final StatementBlock sb2 =
                new StatementBlock(new Statement[]{nullStat, tryStat});
        //create java block
        JavaBlock result = JavaBlock.createJavaBlock(sb2);
        return result;
    }


    private Term buildProgramTerm(ImmutableList<ProgramVariable> paramVars,
                                  ProgramVariable selfVar,
                                  ProgramVariable resultVar,
                                  ProgramVariable exceptionVar,
                                  LocationVariable heapAtPreVar,
                                  Term postTerm) {

        //create java block
        final JavaBlock jb = buildJavaBlock(paramVars,
                                            selfVar,
                                            resultVar,
                                            exceptionVar);

        //create program term
        final Term programTerm = TB.prog(Modality.BOX, jb, postTerm);

        //create update
        Term update = TB.elementary(services, TB.heap(services), TB.var(
                heapAtPreVar));
//        Iterator<LocationVariable> formalParamIt = formalParamVars.iterator();
//        Iterator<ProgramVariable> paramIt        = paramVars.iterator();
//        while(formalParamIt.hasNext()) {
//            Term paramUpdate = TB.elementary(services, 
//        	    			     formalParamIt.next(), 
//        	    			     TB.var(paramIt.next()));
//            update = TB.parallel(update, paramUpdate);
//        }

        return TB.apply(update, programTerm);
    }

    //-------------------------------------------------------------------------
    //public interface
    //-------------------------------------------------------------------------        

    @Override
    public void readProblem()
            throws ProofInputException {
        try {
            final ProgramMethod pm = getContract().getTarget();
            final ProofObligationVariables vs = new ProofObligationVariables(pm);

            // often used terms
            final Term updateHeapAtPre1 =
                    TB.elementary(services,
                                  TB.heap(services),
                                  TB.var(vs.heapAtPreVar1));
            final Term updateHeapAtPre2 =
                    TB.elementary(services,
                                  TB.heap(services),
                                  TB.var(vs.heapAtPreVar2));
            final Term updateHeapAtPost1 =
                    TB.elementary(services,
                                  TB.heap(services),
                                  TB.var(vs.heapAtPostVar1));
            final Term updateHeapAtPost2 =
                    TB.elementary(services,
                                  TB.heap(services),
                                  TB.var(vs.heapAtPostVar2));

            // build precondition
            final Term freePre =
                    buildFreePre(vs, contract.getKJT(), updateHeapAtPre1,
                                 updateHeapAtPre2);
            final Term pre1 =
                    TB.apply(updateHeapAtPre1,
                             contract.getPre(vs.selfVar,
                                             vs.paramVars1,
                                             services));
            final Term pre2 =
                    TB.apply(updateHeapAtPre2,
                             contract.getPre(vs.selfVar,
                                             vs.paramVars2,
                                             services));
            final Term pre = TB.and(freePre, pre1, pre2);

            // build second program term
            final Term postSecondProg = TB.parseTerm(
                    "result2 = resultValue & heapAtPost2 = heap", services);
            final Term secondProg = buildProgramTerm(vs.paramVars2, vs.selfVar,
                                                     vs.resultValueVar,
                                                     vs.exceptionVar2,
                                                     vs.heapAtPreVar2,
                                                     postSecondProg);

            // build first program term
            final Term postfirstProg = TB.parseTerm(
                    "result1 = resultValue & heapAtPost1 = heap", services);
            final Term firstProg = buildProgramTerm(vs.paramVars1, vs.selfVar,
                                                    vs.resultValueVar,
                                                    vs.exceptionVar1,
                                                    vs.heapAtPreVar1, TB.and(
                    postfirstProg, secondProg));

            // build post
            final Term inOutRelations = buildInputOutputRelations(vs);

            final LinkedHashMap<Term, Term> heapReplaceMap1 =
                    new LinkedHashMap<Term, Term>(TB.heap(services),
                                                  TB.var(vs.heapAtPreVar1));
            final Term modContract1 =
                    getContract().getMod(vs.selfVar, vs.paramVars1, services);
            final Term frame1Tail =
                    TB.frame(services, heapReplaceMap1, modContract1);
            final Term frame1 = TB.apply(updateHeapAtPost1, frame1Tail);

            final LinkedHashMap<Term, Term> heapReplaceMap2 =
                    new LinkedHashMap<Term, Term>(TB.heap(services),
                                                  TB.var(vs.heapAtPreVar2));
            final Term modContract2 =
                    getContract().getMod(vs.selfVar, vs.paramVars2, services);
            final Term frame2Tail =
                    TB.frame(services, heapReplaceMap2, modContract2);
            final Term frame2 = TB.apply(updateHeapAtPost2, frame2Tail);

            final Term post = TB.and(inOutRelations, frame1, frame2);

            // create and assign final problem term
            poTerms = new Term[]{
                        TB.imp(TB.and(pre, firstProg), post)
                    };

            // add axioms
            collectClassAxioms(contract.getKJT());

        } catch (ParserException e) {
            assert (false) : e.toString();
        }
    }


    @Override
    public boolean implies(ProofOblInput po) {
        if (!(po instanceof InformationFlowContractPO)) {
            return false;
        }
        InformationFlowContractPO cPO = (InformationFlowContractPO) po;
        return contract.equals(cPO.contract);
    }


    @Override
    public InformationFlowContract getContract() {
        return (InformationFlowContract) contract;
    }


    @Override
    public Term getMbyAtPre() {
        return mbyAtPre;
    }


    @Override
    public boolean equals(Object o) {
        if (!(o instanceof InformationFlowContractPO)) {
            return false;
        } else {
            return contract.equals(((InformationFlowContractPO) o).contract);
        }
    }


    @Override
    public int hashCode() {
        return contract.hashCode();
    }


    @Override
    protected Term generateSelfNotNull(ProgramVariable selfVar) {
        return selfVar == null || getContract().getTarget().isConstructor()
               ? TB.tt()
               : TB.not(TB.equals(TB.var(selfVar), TB.NULL(services)));
    }


    @Override
    protected Term generateSelfCreated(ProgramVariable selfVar) {
        return selfVar == null || getContract().getTarget().isConstructor()
               ? TB.tt()
               : TB.created(services, TB.var(selfVar));
    }


    @Override
    protected Term generateSelfExactType(ProgramVariable selfVar,
                                         KeYJavaType selfKJT) {
        if (selfVar == null || getContract().getTarget().isConstructor()) {
            return TB.tt();
        } else {
            return TB.exactInstance(services, selfKJT.getSort(), TB.var(selfVar));
        }
    }


    @Override
    protected Term generateParamsOK(ImmutableList<ProgramVariable> paramVars) {
        Term paramsOK = TB.tt();
        for (ProgramVariable paramVar : paramVars) {
            paramsOK = TB.and(paramsOK, TB.reachableValue(services, paramVar));
        }
        return paramsOK;
    }


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
     * Prepare program and location variables.
     * 
     * @author christoph
     *
     */
    private class ProofObligationVariables {

        final ProgramVariable selfVar;
        final ImmutableList<ProgramVariable> paramVars1, paramVars2;
        final ProgramVariable resultValueVar, resultVar1, resultVar2;
        final ProgramVariable exceptionVar1, exceptionVar2;
        final LocationVariable heapAtPreVar1, heapAtPreVar2;
        final LocationVariable heapAtPostVar1, heapAtPostVar2;


        ProofObligationVariables(ProgramMethod pm) {
            selfVar = TB.selfVar(services, pm, contract.getKJT(), true);
            paramVars1 = TB.paramVars(services, "_1", pm, true);
            paramVars2 = TB.paramVars(services, "_2", pm, true);
            resultValueVar = TB.resultVar(services, "resultValue", pm, true);
            resultVar1 = TB.resultVar(services, "result1", pm, true);
            resultVar2 = TB.resultVar(services, "result2", pm, true);
            exceptionVar1 = TB.excVar(services, "exc1", pm, true);
            exceptionVar2 = TB.excVar(services, "exc2", pm, true);
            heapAtPreVar1 = TB.heapAtPreVar(services, "heapAtPre1", true);
            heapAtPreVar2 = TB.heapAtPreVar(services, "heapAtPre2", true);
            heapAtPostVar1 = TB.heapAtPreVar(services, "heapAtPost1", true);
            heapAtPostVar2 = TB.heapAtPreVar(services, "heapAtPost2", true);

            //register the variables so they are declared in proof header
            //if the proof is saved to a file
            register(selfVar);
            register(paramVars1);
            register(paramVars2);
            register(resultValueVar);
            register(resultVar1);
            register(resultVar2);
            register(exceptionVar1);
            register(exceptionVar2);
            register(heapAtPreVar1);
            register(heapAtPreVar2);
            register(heapAtPostVar1);
            register(heapAtPostVar2);
        }
    }
}
