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
import de.uka.ilkd.key.java.declaration.modifier.VisibilityModifier;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.proof.init.ContractPO;
import de.uka.ilkd.key.proof.init.InfFlowContractPO;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.util.Triple;

import java.util.Iterator;
import java.util.List;
import java.util.Map;



/**
 * Standard implementation of the DependencyContract interface.
 */
public final class InformationFlowContractImpl implements InformationFlowContract {

    protected static final TermBuilder TB = TermBuilder.DF;
    private final int id;
    private final KeYJavaType forClass;
    private final IProgramMethod pm;
    private final KeYJavaType specifiedIn;
    private final String baseName;
    private final String name;
    private final Term origPre;
    private final Term origMby;
    private final Term origMod;
    private final Modality modality;
    private final Term origSelf;
    private final ImmutableList<Term> origParams;
    private final Term origResult;
    private final Term origExc;
    private final Term origAtPre;
    private final boolean toBeSaved;
    private final Term origDep;
    private final ImmutableList<Triple<ImmutableList<Term>,
                                       ImmutableList<Term>,
                                       ImmutableList<Term>>> origRespects;

    /**
     * If a method is strictly pure, it has no modifies clause which could
     * anonymised.
     * @see #hasModifiesClause()
     */
    final boolean hasRealModifiesClause;

    
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
                                          Term exc,
                                          Term heapAtPre,
                                          Term dep,
                                          ImmutableList<Triple<ImmutableList<Term>,
                                                               ImmutableList<Term>,
                                                               ImmutableList<Term>>> respects,
                                          boolean toBeSaved,
                                          int id) {
        assert baseName != null;
        assert forClass != null;
        assert pm != null;
        assert modality != null;
        assert pre != null;
        assert mod != null;
        assert (self == null) == pm.isStatic();
        assert params != null;
//        assert params.size() == pm.getParameterDeclarationCount();
        if (result == null){
            assert (pm.isVoid() || pm.isConstructor()) : "resultVar == null for method "+pm;
        } else {
            assert (!pm.isVoid() && !pm.isConstructor())
                : "non-null result variable for void method or constructor "+
                    pm+" with return type "+pm.getReturnType();
        }
        assert exc != null;
//        assert dep != null;
        assert respects != null;

        this.baseName = baseName;
        this.name = name != null
                    ? name
                    : ContractFactory.generateContractName(baseName, forClass, pm, specifiedIn, id);
        this.forClass = forClass;
        this.pm = pm;
        this.specifiedIn = specifiedIn;
        this.origPre = pre;
        this.origMby = mby;
        this.origMod = mod;
        this.origSelf = self;
        this.origParams = params;
        this.origResult = result;
        this.origExc = exc;
        this.origAtPre = heapAtPre;
        this.id = id;
        this.modality = modality;
        this.hasRealModifiesClause  = hasRealMod;
        this.toBeSaved = toBeSaved;
        this.origDep = dep;
        this.origRespects = respects;
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
                                       Term exc,
                                       Term heapAtPre,
                                       Term dep,
                                       ImmutableList<Triple<ImmutableList<Term>,
                                                            ImmutableList<Term>,
                                                            ImmutableList<Term>>> respects,
                                       boolean toBeSaved) {
        this(baseName, null, forClass, pm, specifiedIn, modality, pre, mby, mod,
             hasRealMod, self, params, result, exc, heapAtPre, dep, respects,
             toBeSaved, INVALID_ID);
    }


    public InformationFlowContractImpl(BlockContract bc, Services services) {

        this(bc.getName(), null, bc.getKJT(), bc.getMethod(), bc.getTarget().getContainerType(),
             bc.getModality(), bc.getPre(services), null, bc.getMod(services),
             bc.hasModifiesClause(), bc.getVariablesAsTerms().self,
             ImmutableSLList.<Term>nil(), bc.getVariablesAsTerms().result,
             bc.getVariablesAsTerms().exception, TB.var(bc.getVariables()
                     .combineRemembranceVariables().get(services.getTypeConverter()
                             .getHeapLDT().getHeap())), null, bc.getRespects(),
             false, bc.getBlock().getStartPosition().getLine());
    }
    
    
    public InformationFlowContractImpl(LoopInvariant li, Services services) {

        this(li.getName(), null, li.getKJT(), li.getTarget(), li.getTarget().getContainerType(),
             Modality.BOX, li.getInvariant(services), null, li.getModifies(),
             (li.getModifies() != TB.strictlyNothing()), li.getInternalSelfTerm(),
             ImmutableSLList.<Term>nil(), null,
             TB.var(TB.excVar(services, li.getTarget(), true)),
             li.getInternalAtPres().get(services.getTypeConverter().getHeapLDT().getHeap()),
             null, li.getRespects(services), false, li.getLoop().getStartPosition().getLine());
    }



    //-------------------------------------------------------------------------
    //public interface
    //-------------------------------------------------------------------------    

    @Override
    public String getName() {
        return name;
    }


    @Override
    public int id() {
        return id;
    }


    @Override
    public KeYJavaType getKJT() {
        return forClass;
    }


    @Override
    public IProgramMethod getTarget() {
        return pm;
    }


    @Override
    public boolean hasMby() {
        return origMby != null;
    }

    
    @Override
    public String getBaseName() {
        return baseName;
    }

    
    @Override
    public Term getPre() {
        return origPre;
    }

    
    @Override
    public Term getMod() {
        return origMod;
    }

    
    @Override
    public Term getMby() {
        return origMby;
    }

    
    @Override
    public Modality getModality() {
        return modality;
    }


    @Override
    public Term getSelf() {
        if (origSelf == null){
            assert pm.isStatic() : "missing self variable in non-static method contract";
            return null;
        }
        return origSelf;
    }

    
    @Override
    public ImmutableList<Term> getParams() {
        return origParams;
    }


    @Override
    public Term getResult() {
        return origResult;
    }
    

    @Override
    public Term getExc() {
        return origExc;
    }


    @Override
    public Term getAtPre() {
        return origAtPre;
    }


    @Override
    public boolean isReadOnlyContract() {
        return origMod.toString().equals("empty");
    }


    @Override
    public String getTypeName() {
        return ContractFactory.generateContractTypeName(baseName, forClass, pm,
                                                        specifiedIn);
    }


    @Override
    public boolean hasModifiesClause() {
        return hasRealModifiesClause;
    }
    
    
    @Override
    public boolean hasRespects() {
        return !origRespects.isEmpty();
    }


    @Override
    public String getHTMLText(Services services) {
        return "<html>"
               + getHTMLBody(services)
               + "</html>";
    }

    
    public String getHTMLBody(Services services) {
        return "<html>"
               + getHTMLSignature()
               + getHTMLFor(origPre, "pre", services)
               + getHTMLFor(origMod, "mod", services)
               + (hasRealModifiesClause ? "" : "<b>, creates no new objects</b>")
               + getHTMLFor(origMby, "measured-by", services)
               + "<br><b>termination</b> " + modality
               + getHTMLFor(origRespects, "segregates", services)
               + "</html>";
    }


    private String getHTMLSignature() {
        return "<i>" + LogicPrinter.escapeHTML(getHTMLSignatureBody().toString(),
                                               false) + "</i>";
    }

    
    private StringBuffer getHTMLSignatureBody() {
        final StringBuffer sig = new StringBuffer();
	if(origResult != null) {
	    sig.append(origResult);
	    sig.append(" = ");
	} else if(pm.isConstructor()) {
	    sig.append(origSelf);
	    sig.append(" = new ");
	}
        if (!pm.isStatic() && !pm.isConstructor()) {
	    sig.append(origSelf);
	    sig.append(".");
	}
	sig.append(pm.getName());
	sig.append("(");
        for (Term pv : origParams) {
	    sig.append(pv.toString()).append(", ");
	}
        if (!origParams.isEmpty()) {
	    sig.setLength(sig.length() - 2);
	}
	sig.append(")");
        sig.append(" catch(");
        sig.append(origExc);
	sig.append(")");
        return sig;
    }

        
    protected String getHTMLFor(Term originalTerm,
                                String htmlName,
                                Services services) {
        if (originalTerm == null) {
            return "";
        } else {
            final String quickPrint =
                    LogicPrinter.quickPrintTerm(originalTerm, services);
            return "<br>"
                   + "<b>" + htmlName + "</b> "
                   + LogicPrinter.escapeHTML(quickPrint, false);
        }
    }


    private String getHTMLFor(Iterable<Term> originalTerms,
                              Services services) {
        String result = "";
        Iterator<Term> it = originalTerms.iterator();
        while (it.hasNext()) {
            Term term = it.next();
            final String quickPrint =
                    LogicPrinter.quickPrintTerm(term, services);
            result += " " + LogicPrinter.escapeHTML(quickPrint, false);
            if (it.hasNext()) {
                result += ", ";
            }
        }
        return result;
    }

    
    private String getHTMLFor(ImmutableList<Triple<ImmutableList<Term>,
                                                   ImmutableList<Term>,
                                                   ImmutableList<Term>>> originalTerms,
                              String htmlName,
                              Services services) {
        String respects = "";
        if (hasRespects()) {
            respects = "<br><b>" + htmlName + "</b> ";
            for (Triple<ImmutableList<Term>,
                        ImmutableList<Term>,
                        ImmutableList<Term>> pair : originalTerms) {
                respects += "(" + getHTMLFor(pair.first, services) + ")";
                if (!pair.second.isEmpty()) {
                    respects += ", declassifies (" + getHTMLFor(pair.second, services) + ")";
                }
                if (!pair.third.isEmpty()) {
                    respects += ", erases (" + getHTMLFor(pair.third, services) + ")";
                }
            }
        }
        return respects;
    }
    

    @Override
    public String toString() {
        // TODO: all fields should be printed!!
        return name + ":: kjt: " + forClass + "; pm: " + pm + "; modality: "
               + modality + "; pre: " + origPre + "; mby: " + origMby
               + "; mod: " + origMod + "; selfVar: " + origSelf
               + "; paramVars: " + origParams + "; id:" + id;
    }


    @Override
    public ContractPO createProofObl(InitConfig initConfig) {
        return new InfFlowContractPO(initConfig, this);
    }


    @Override
    public ProofOblInput getProofObl(Services services) {
        return services.getSpecificationRepository().getPO(this);
    }


    @Override
    public String getDisplayName() {
        return ContractFactory.generateDisplayName(baseName, forClass, pm,
                                                   specifiedIn, id);
    }

    @Override
    public String getPODisplayName() {
        return "Method Contract";
    }


    @Override
    public VisibilityModifier getVisibility() {
        assert false; // this is currently not applicable for contracts
        return null;
    }


    @Override
    public boolean transactionApplicableContract() {
        return false;
    }

    
    @Override
    public KeYJavaType getSpecifiedIn() {
        return specifiedIn;
    }

    
    @Override
    public InformationFlowContract setID(int newId) {
        return new InformationFlowContractImpl(baseName, null, forClass, pm,
                                               specifiedIn, modality, origPre,
                                               origMby, origMod,
                                               hasRealModifiesClause, origSelf,
                                               origParams, origResult, origExc,
                                               origAtPre, origDep, origRespects,
                                               toBeSaved, newId);
    }


    @Override
    public InformationFlowContract setTarget(KeYJavaType newKJT,
                                             IObserverFunction newPM) {
        assert newPM instanceof IProgramMethod;
        return new InformationFlowContractImpl(baseName, null, newKJT,
                                               (IProgramMethod)newPM,
                                               specifiedIn, modality, origPre,
                                               origMby, origMod,
                                               hasRealModifiesClause, origSelf,
                                               origParams, origResult, origExc,
                                               origAtPre, origDep, origRespects,
                                               toBeSaved, id);
    }


    @Override
    public InformationFlowContract setName(String name) {
        return new InformationFlowContractImpl(baseName, name, forClass, pm,
                                               specifiedIn, modality, origPre,
                                               origMby, origMod,
                                               hasRealModifiesClause, origSelf,
                                               origParams, origResult, origExc,
                                               origAtPre, origDep, origRespects,
                                               toBeSaved, id);
    }


    @Override
    public InformationFlowContract setModality(Modality modality) {
        return new InformationFlowContractImpl(baseName, name, forClass, pm,
                                               specifiedIn, modality, origPre,
                                               origMby, origMod,
                                               hasRealModifiesClause, origSelf,
                                               origParams, origResult, origExc,
                                               origAtPre, origDep, origRespects,
                                               toBeSaved, id);
    }


    @Override
    public InformationFlowContract setModifies(Term modifies) {
        return new InformationFlowContractImpl(baseName, name, forClass, pm,
                                               specifiedIn, modality, origPre,
                                               origMby, modifies,
                                               hasRealModifiesClause, origSelf,
                                               origParams, origResult, origExc,
                                               origAtPre, origDep, origRespects,
                                               toBeSaved, id);
    }


    @Override
    public Term getDep() {
        return origDep;
    }


    @Override
    public ImmutableList<Triple<ImmutableList<Term>,
                                ImmutableList<Term>,
                                ImmutableList<Term>>> getRespects() {
        return origRespects;
    }


    @Override
    public boolean equals(Contract c) {
        if (c == null || !(c instanceof InformationFlowContract)) {
            return false;
        }
        assert name != null;
        assert forClass != null;
        assert pm != null;
        assert modality != null;
        assert origPre != null;
        assert origMod != null;
        assert origParams != null;
        assert origDep != null;
        assert origRespects != null;
        InformationFlowContract ifc = (InformationFlowContract) c;
        return name.equals(ifc.getName())
               && forClass.equals(ifc.getKJT())
               && pm.equals(ifc.getTarget())
               && modality.equals(ifc.getModality())
               && origPre.equals(ifc.getPre())
               && (origMby != null
                   ? origMby.equals(ifc.getMby())
                   : ifc.getMby() == null)
               && origMod.equals(ifc.getMod())
               && (origSelf != null
                   ? origSelf.equals(ifc.getSelf())
                   : ifc.getSelf() == null)
               && origParams.equals(ifc.getParams())
               && (origResult != null
                   ? origResult.equals(ifc.getResult())
                   : ifc.getResult() == null)
               && origExc.equals(ifc.getExc())
               && origAtPre.equals(ifc.getAtPre())
               && id == ifc.id()
               && toBeSaved == ifc.toBeSaved()
               && origDep.equals(ifc.getDep())
               && origRespects.equals(ifc.getRespects());
    }
    
    
    @Override
    public boolean toBeSaved() {
        return false;   // because information flow contracts currently cannot
                        // be specified directly in DL
    }


    @Override
    public String proofToString(Services services) {
        throw new UnsupportedOperationException("Operation not supported.");
    }


    @Override
    public String getPlainText(Services services) {
        return getHTMLText(services); // TODO: return real plaintext...
    }



    // the following code is legacy code
    
    @Override
    @Deprecated
    public Term getPre(LocationVariable heap,
                       ProgramVariable selfVar,
                       ImmutableList<ProgramVariable> paramVars,
                       Map<LocationVariable, ? extends ProgramVariable> atPreVars,
                       Services services) {
                throw new UnsupportedOperationException("Not supported any more. "
                + "Please use the POSnippetFactory instead.");
    }

    @Override
    @Deprecated
    public Term getPre(List<LocationVariable> heapContext,
                       ProgramVariable selfVar,
                       ImmutableList<ProgramVariable> paramVars,
                       Map<LocationVariable, ? extends ProgramVariable> atPreVars,
                       Services services) {
                throw new UnsupportedOperationException("Not supported any more. "
                + "Please use the POSnippetFactory instead.");

    }

    @Override
    @Deprecated
    public Term getPre(LocationVariable heap,
                       Term heapTerm,
                       Term selfTerm,
                       ImmutableList<Term> paramTerms,
                       Map<LocationVariable, Term> atPres,
                       Services services) {
        throw new UnsupportedOperationException("Not supported any more. "
                + "Please use the POSnippetFactory instead.");

    }

    @Override
    @Deprecated
    public Term getPre(List<LocationVariable> heapContext,
                       Map<LocationVariable, Term> heapTerms,
                       Term selfTerm,
                       ImmutableList<Term> paramTerms,
                       Map<LocationVariable, Term> atPres,
                       Services services) {
        throw new UnsupportedOperationException("Not supported any more. "
                + "Please use the POSnippetFactory instead.");

    }

    @Override
    @Deprecated
    public Term getMby(ProgramVariable selfVar,
                       ImmutableList<ProgramVariable> paramVars,
                       Services services) {
        throw new UnsupportedOperationException("Not supported any more. "
                + "Please use the POSnippetFactory instead.");
    }

    
    @Override
    @Deprecated
    public Term getMby(Term heapTerm,
                       Term selfTerm,
                       ImmutableList<Term> paramTerms,
                       Services services) {
        throw new UnsupportedOperationException("Not supported any more. "
                + "Please use the POSnippetFactory instead.");
    }

}
