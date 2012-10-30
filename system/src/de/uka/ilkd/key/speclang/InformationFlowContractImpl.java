// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.speclang;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.ObserverFunction;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.proof.init.ContractPO;
import de.uka.ilkd.key.proof.init.InformationFlowContractPO;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.SymbolicExecutionPO;



/**
 * Standard implementation of the DependencyContract interface.
 */
final class InformationFlowContractImpl extends SymbolicExecDataImpl
        implements InformationFlowContract {

    private final Term origDep;
    private final ImmutableList<ImmutableList<Term>> origRespects;
    private final ImmutableList<ImmutableList<Term>> origDeclassify;
    SymbolicExecData symExecData;

    //-------------------------------------------------------------------------
    //constructors
    //-------------------------------------------------------------------------

    protected InformationFlowContractImpl(String baseName,
                                          String name,
                                          KeYJavaType forClass,
                                          IProgramMethod pm,
                                          KeYJavaType specifiedIn,
                                          Modality modality,
                                          Term pre,
                                          Term mby,
                                          Term mod,
                                          boolean hasRealMod,
                                          Term self,
                                          ImmutableList<Term> params,
                                          Term result,
                                          Term exec,
                                          Term dep,
                                          ImmutableList<ImmutableList<Term>> respects,
                                          ImmutableList<ImmutableList<Term>> declassify,
                                          boolean toBeSaved,
                                          int id) {
        super(baseName, name, forClass, pm, specifiedIn, modality, pre, mby, mod,
              hasRealMod, self, params, result, exec, toBeSaved, id);

        assert dep != null;
        assert respects != null;
        assert declassify != null;

        this.origDep = dep;
        this.origRespects = respects;
        this.origDeclassify = declassify;
    }


    public InformationFlowContractImpl(String baseName,
                                       KeYJavaType forClass,
                                       IProgramMethod pm,
                                       KeYJavaType specifiedIn,
                                       Modality modality,
                                       Term pre,
                                       Term mby,
                                       Term mod,
                                       boolean hasRealMod,
                                       Term self,
                                       ImmutableList<Term> params,
                                       Term result,
                                       Term exec,
                                       Term dep,
                                       ImmutableList<ImmutableList<Term>> respects,
                                       ImmutableList<ImmutableList<Term>> declassify,
                                       boolean toBeSaved) {

        this(baseName, null, forClass, pm, specifiedIn, modality, pre, mby, mod,
             hasRealMod, self, params, result, exec, dep, respects, declassify,
             toBeSaved, INVALID_ID);
    }

    

    //-------------------------------------------------------------------------
    //public interface
    //-------------------------------------------------------------------------    
    @Override
    public boolean hasRespects() {
        return !origRespects.isEmpty();
    }


    @Override
    public boolean hasDeclassify() {
        return !origDeclassify.isEmpty();
    }


    @Override
    public Term getDep(Term heapTerm,
                       Term selfTerm,
                       ImmutableList<Term> paramTerms,
                       Services services) {
        assert heapTerm != null;
        assert (selfTerm == null) == (getSelf() == null);
        assert paramTerms != null;
        assert paramTerms.size() == getParams().size();
        assert services != null;
        return TB.replace(origDep, services,
                          TB.getBaseHeap(services), heapTerm,
                          getSelf(), selfTerm,
                          getParams(), paramTerms);
    }


    @Override
    public ImmutableList<ImmutableList<Term>> getRespects(Term heapTerm,
                                           Term selfTerm,
                                           ImmutableList<Term> paramTerms,
                                           Term resultTerm,
                                           Services services) {
        assert heapTerm != null;
        assert (selfTerm == null) == (getSelf() == null);
        assert paramTerms != null;
        assert paramTerms.size() == getParams().size();
        assert services != null;
        ImmutableList<Term> origParamTerms = getParams();
        if (getResult() != null) {
            origParamTerms = origParamTerms.append(getResult());
            paramTerms = paramTerms.append(resultTerm);
        }
        return TB.replace2(origRespects, heapTerm,
                          getSelf(), selfTerm,
                          origParamTerms, paramTerms, services);
    }


    @Override
    public ImmutableList<ImmutableList<Term>> getDeclassify(Term heapTerm,
                                                            Term selfTerm,
                                                            ImmutableList<Term> paramTerms,
                                                            Term resultTerm,
                                                            Services services) {
        assert heapTerm != null;
        assert (selfTerm == null) == (getSelf() == null);
        assert paramTerms != null;
        assert paramTerms.size() == getParams().size();
        assert services != null;
        ImmutableList<Term> origParamTerms = getParams();
        if (getResult() != null) {
            origParamTerms = origParamTerms.append(getResult());
            paramTerms = paramTerms.append(resultTerm);
        }
        return TB.replace2(origDeclassify, heapTerm,
                           getSelf(), selfTerm,
                           origParamTerms, paramTerms, services);
    }


    @Override
    public String getHTMLText(Services services) {
        return "<html>"
               + getHTMLBody(services)
               + "</html>";
    }


    @Override
    public String getHTMLBody(Services services) {
        return "<html>"
               + super.getHTMLBody(services)
               + getHTMLFor2(origRespects, "respects", services)
               + getHTMLForDeclassify(services)
               + "</html>";
    }


    private String getHTMLFor(Iterable<Term> originalTerms,
                              String htmlName,
                              Services services) {
        String respects = "";
        if (hasRespects()) {
            respects = "<br><b>" + htmlName + "</b> ";
            for (Term term : originalTerms) {
                final String quickPrint =
                        LogicPrinter.quickPrintTerm(term, services);
                respects += LogicPrinter.escapeHTML(quickPrint, false);
            }
        }
        return respects;
    }

    
    private String getHTMLFor2(Iterable<ImmutableList<Term>> originalTerms,
                              String htmlName,
                              Services services) {
        String respects = "";
        if (hasRespects()) {
            respects = "<br><b>" + htmlName + "</b> ";
            for (Iterable<Term> list : originalTerms) {
                respects += "(" + getHTMLFor(list, htmlName, services) + ") ";
            }
        }
        return respects;
    }
    

    private String getHTMLForDeclassify(Services services) {
        String declassify = "";
        if (hasDeclassify()) {
            final String quickPrint =
                    LogicPrinter.quickPrintTerm(
                    origDeclassify.head().head(),
                    services);
            declassify = "<br><b>declassify</b> ";
            declassify += LogicPrinter.escapeHTML(quickPrint, false);
        }
        return declassify;
    }


    @Override
    public String toString() {
        // TODO: all fields should be printed!!
        return super.toString();
    }


    @Override
    public boolean toBeSaved() {
        return false;   // because information flow contracts currently cannot
        // be specified directly in DL
    }


    @Override
    public String proofToString(Services services) {
        assert false;
        return null;
    }


    @Override
    public ContractPO createProofObl(InitConfig initConfig) {
        return new InformationFlowContractPO(initConfig, this);
    }


    @Override
    public InformationFlowContract setID(int newId) {
        SymbolicExecData op = super.setID(newId);
        return new InformationFlowContractImpl(op.getBaseName(), op.getName(),
                                               op.getKJT(), op.getTarget(),
                                               op.getSpecifiedIn(),
                                               op.getModality(),
                                               op.getPre(), op.getMby(),
                                               op.getMod(),
                                               op.hasModifiesClause(),
                                               op.getSelf(),
                                               op.getParams(),
                                               op.getResult(),
                                               op.getExc(),
                                               origDep,
                                               origRespects,
                                               origDeclassify,
                                               op.toBeSaved(),
                                               op.id());
    }


    @Override
    public InformationFlowContract setTarget(KeYJavaType newKJT,
                                             ObserverFunction newPM) {
        SymbolicExecData op = super.setTarget(newKJT, newPM);
        return new InformationFlowContractImpl(op.getBaseName(), op.getName(),
                                               op.getKJT(), op.getTarget(),
                                               op.getSpecifiedIn(),
                                               op.getModality(),
                                               op.getPre(), op.getMby(),
                                               op.getMod(),
                                               op.hasModifiesClause(),
                                               op.getSelf(),
                                               op.getParams(),
                                               op.getResult(),
                                               op.getExc(),
                                               origDep,
                                               origRespects,
                                               origDeclassify,
                                               op.toBeSaved(),
                                               op.id());
    }


    @Override
    public InformationFlowContract andPre(Term pre,
                                          Term usedSelf,
                                          ImmutableList<Term> usedoldParams,
                                          Services services) {
        SymbolicExecData op = super.andPre(pre, usedSelf, usedoldParams,
                                            services);
        return new InformationFlowContractImpl(op.getBaseName(), op.getName(),
                                               op.getKJT(), op.getTarget(),
                                               op.getSpecifiedIn(),
                                               op.getModality(),
                                               op.getPre(), op.getMby(),
                                               op.getMod(),
                                               op.hasModifiesClause(),
                                               op.getSelf(),
                                               op.getParams(),
                                               op.getResult(),
                                               op.getExc(),
                                               origDep,
                                               origRespects,
                                               origDeclassify,
                                               op.toBeSaved(),
                                               op.id());
    }


    @Override
    public InformationFlowContract orPre(Term pre,
                                         Term usedSelf,
                                         ImmutableList<Term> usedParams,
                                         Services services) {
        SymbolicExecData op = super.orPre(pre, usedSelf, usedParams, services);
        return new InformationFlowContractImpl(op.getBaseName(), op.getName(),
                                               op.getKJT(), op.getTarget(),
                                               op.getSpecifiedIn(),
                                               op.getModality(),
                                               op.getPre(), op.getMby(),
                                               op.getMod(),
                                               op.hasModifiesClause(),
                                               op.getSelf(),
                                               op.getParams(),
                                               op.getResult(),
                                               op.getExc(),
                                               origDep,
                                               origRespects,
                                               origDeclassify,
                                               op.toBeSaved(),
                                               op.id());
    }


    @Override
    public InformationFlowContract addMby(Term condition,
                                          Term mby) {
        SymbolicExecData op = super.addMby(condition, mby);
        return new InformationFlowContractImpl(op.getBaseName(), op.getName(),
                                               op.getKJT(), op.getTarget(),
                                               op.getSpecifiedIn(),
                                               op.getModality(),
                                               op.getPre(), op.getMby(),
                                               op.getMod(),
                                               op.hasModifiesClause(),
                                               op.getSelf(),
                                               op.getParams(),
                                               op.getResult(),
                                               op.getExc(),
                                               origDep,
                                               origRespects,
                                               origDeclassify,
                                               op.toBeSaved(),
                                               op.id());
    }


    @Override
    public InformationFlowContract addMod(Term mod,
                                          Services services) {
        SymbolicExecData op = super.addMod(mod, services);
        return new InformationFlowContractImpl(op.getBaseName(), op.getName(),
                                               op.getKJT(), op.getTarget(),
                                               op.getSpecifiedIn(),
                                               op.getModality(),
                                               op.getPre(), op.getMby(),
                                               op.getMod(),
                                               op.hasModifiesClause(),
                                               op.getSelf(),
                                               op.getParams(),
                                               op.getResult(),
                                               op.getExc(),
                                               origDep,
                                               origRespects,
                                               origDeclassify,
                                               op.toBeSaved(),
                                               op.id());
    }


    @Override
    public InformationFlowContract setName(String name) {
        SymbolicExecData op = super.setName(name);
        return new InformationFlowContractImpl(op.getBaseName(), op.getName(),
                                               op.getKJT(), op.getTarget(),
                                               op.getSpecifiedIn(),
                                               op.getModality(),
                                               op.getPre(), op.getMby(),
                                               op.getMod(),
                                               op.hasModifiesClause(),
                                               op.getSelf(),
                                               op.getParams(),
                                               op.getResult(),
                                               op.getExc(),
                                               origDep,
                                               origRespects,
                                               origDeclassify,
                                               op.toBeSaved(),
                                               op.id());
    }


    @Override
    public InformationFlowContract setModality(Modality modality) {
        SymbolicExecData op = super.setModality(modality);
        return new InformationFlowContractImpl(op.getBaseName(), op.getName(),
                                               op.getKJT(), op.getTarget(),
                                               op.getSpecifiedIn(),
                                               op.getModality(),
                                               op.getPre(), op.getMby(),
                                               op.getMod(),
                                               op.hasModifiesClause(),
                                               op.getSelf(),
                                               op.getParams(),
                                               op.getResult(),
                                               op.getExc(),
                                               origDep,
                                               origRespects,
                                               origDeclassify,
                                               op.toBeSaved(),
                                               op.id());
    }


    @Override
    public InformationFlowContract setModifies(Term modifies) {
        SymbolicExecData op = super.setModifies(modifies);
        return new InformationFlowContractImpl(op.getBaseName(), op.getName(),
                                               op.getKJT(), op.getTarget(),
                                               op.getSpecifiedIn(),
                                               op.getModality(),
                                               op.getPre(), op.getMby(),
                                               op.getMod(),
                                               op.hasModifiesClause(),
                                               op.getSelf(),
                                               op.getParams(),
                                               op.getResult(),
                                               op.getExc(),
                                               origDep,
                                               origRespects,
                                               origDeclassify,
                                               op.toBeSaved(),
                                               op.id());
    }


    @Override
    public SymbolicExecData getSymbExecData(Services services) {
        int n = 0;
        String name = ContractFactory.generateContractName(
                    ContractFactory.SYMB_EXEC_CONTRACT_BASENAME, getKJT(),
                    getTarget(), getSpecifiedIn(), n);
        while(name != null) {
            SymbolicExecData data =
                    (SymbolicExecData) services.getSpecificationRepository().getContractByName(
                    name);
            if (equalsData(data)) {
                return data;
            } else {
                n++;
                name = ContractFactory.generateContractName(
                        ContractFactory.SYMB_EXEC_CONTRACT_BASENAME, getKJT(),
                        getTarget(), getSpecifiedIn(), n);
            }
        }
        throw new RuntimeException("Could not find symbolic exection data for "
                + getName());
    }


    @Override
    public Term getDep() {
        return origDep;
    }


    @Override
    public ImmutableList<ImmutableList<Term>> getRespects() {
        return origRespects;
    }


    @Override
    public ImmutableList<ImmutableList<Term>> getDeclassify() {
        return origDeclassify;
    }


    @Override
    public boolean equals(Contract c) {
        if (c == null || !(c instanceof InformationFlowContract)) {
            return false;
        }
        assert origDep != null;
        assert origRespects != null;
        assert origDeclassify != null;
        InformationFlowContract ifc = (InformationFlowContract) c;
        return super.equals(c)
               && origDep.equals(ifc.getDep())
               && origRespects.equals(ifc.getRespects())
               && origDeclassify.equals(ifc.getDeclassify());
    }
    
    
    @Override
    public ImmutableList<Contract> getContractsToBeStartedBefore(Services services) {
        SymbolicExecData symbExecCont = getSymbExecData(services);
        SymbolicExecutionPO symbExecPO = symbExecCont.getProofObl(services);
        if (symbExecPO == null) {
            return ImmutableSLList.<Contract>nil().append(symbExecCont);
        } else {
            return ImmutableSLList.<Contract>nil();
        }
    }
}
