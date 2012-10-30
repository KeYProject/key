/*
 * To change this template, choose Tools | Templates and open the template in
 * the editor.
 */
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
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.init.SymbolicExecutionPO;
import java.util.List;
import java.util.Map;



/**
 *
 * @author scheben
 */
class SymbolicExecDataImpl implements SymbolicExecData {

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
    private final Modality poModality;
    private final Term origSelf;
    private final ImmutableList<Term> origParams;
    private final Term origResult;
    private final Term origExc;
    private final boolean origToBeSaved;
    


    /**
     * If a method is strictly pure, it has no modifies clause which could
     * anonymised.
     * @see #hasModifiesClause()
     */
    final boolean hasRealModifiesClause;
    

    //-------------------------------------------------------------------------
    //constructors
    //-------------------------------------------------------------------------

    protected SymbolicExecDataImpl(String baseName,
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
        assert params.size() == pm.getParameterDeclarationCount();
        if (result == null){
            assert (pm.isVoid() || pm.isConstructor()) : "resultVar == null for method "+pm;
        } else {
            assert (!pm.isVoid() && !pm.isConstructor()) : "non-null result variable for void method or constructor "+pm+" with return type "+pm.getReturnType();
        }
        assert exc != null;

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
        this.id = id;
        this.modality = modality;
        this.poModality = (modality == Modality.DIA_TRANSACTION ? Modality.DIA
                           : (modality == Modality.BOX_TRANSACTION
                              ? Modality.BOX : modality));
        this.hasRealModifiesClause  = hasRealMod;
        this.origToBeSaved = toBeSaved;
    }


    SymbolicExecDataImpl(String baseName,
                          KeYJavaType kjt,
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
                          boolean toBeSaved) {
        this(baseName, null, kjt, pm, specifiedIn, modality, pre, mby, mod,
             hasRealMod, self, params, result, exc, toBeSaved, INVALID_ID);
    }

    
    //-------------------------------------------------------------------------
    //private interface
    //-------------------------------------------------------------------------    
    protected static <T> ImmutableList<T> ops(ImmutableList<Term> terms,
                                              Class<T> opClass)
            throws IllegalArgumentException {
        ImmutableList<T> ops = ImmutableSLList.<T>nil();
        for (Term t : terms) {
            ops = ops.append(t.op(opClass));
        }
        return ops;
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
    public Term getPre(Term heapTerm,
                       Term selfTerm,
                       ImmutableList<Term> paramTerms,
                       Services services) {
        assert heapTerm != null;
        assert (selfTerm == null) == (origSelf == null);
        assert paramTerms != null;
        assert paramTerms.size() == origParams.size();
        assert services != null;
        return TB.replace(origPre, services,
                          TB.getBaseHeap(services), heapTerm,
                          getSelf(), selfTerm,
                          getParams(), paramTerms);
    }


    @Override
    public Term getMby(Term heapTerm,
                       Term selfTerm,
                       ImmutableList<Term> paramTerms,
                       Services services) {
        assert hasMby();
        assert heapTerm != null;
        assert (selfTerm == null) == (origSelf == null);
        assert paramTerms != null;
        assert paramTerms.size() == origParams.size();
        assert services != null;
        return TB.replace(origMby, services,
                          TB.getBaseHeap(services), heapTerm,
                          getSelf(), selfTerm,
                          getParams(), paramTerms);
    }


    @Override
    public Term getMod(Term heapTerm,
                       Term selfTerm,
                       ImmutableList<Term> paramTerms,
                       Services services) {
        assert heapTerm != null;
        assert (selfTerm == null) == (origSelf == null);
        assert paramTerms != null;
        assert paramTerms.size() == origParams.size();
        assert services != null;
        return TB.replace(origMod, services,
                          TB.getBaseHeap(services), heapTerm,
                          getSelf(), selfTerm,
                          getParams(), paramTerms);
    }


    @Override
    public SymbolicExecData setID(int newId) {
        return new SymbolicExecDataImpl(baseName, null, forClass, pm,
                                        specifiedIn, modality, origPre, origMby,
                                        origMod, hasRealModifiesClause,
                                        origSelf, origParams,
                                        origResult, origExc,
                                        origToBeSaved, newId);
    }


    @Override
    public SymbolicExecData setTarget(KeYJavaType newKJT,
                                      IObserverFunction newPM) {
        assert newPM instanceof ProgramMethod;
        return new SymbolicExecDataImpl(baseName, null, newKJT,
                                         (ProgramMethod) newPM, specifiedIn,
                                         modality, origPre, origMby,
                                         origMod, hasRealModifiesClause,
                                         origSelf,
                                         origParams, origResult, origExc,
                                         origToBeSaved, id);
    }


    @Override
    public SymbolicExecData andPre(Term pre,
                                    Term usedSelf,
                                    ImmutableList<Term> usedParams,
                                    Services services) {
        pre = TB.replace(pre, services, usedSelf,
                         getSelf(),
                         usedParams, getParams());
        return new SymbolicExecDataImpl(baseName, name, forClass, pm,
                                        specifiedIn, modality,
                                        TB.and(origPre, pre), origMby,
                                        origMod, hasRealModifiesClause,
                                        origSelf,
                                        origParams, origResult, origExc,
                                        origToBeSaved, id);
    }


    @Override
    public SymbolicExecData orPre(Term pre,
                                   Term usedSelf,
                                   ImmutableList<Term> usedParams,
                                   Services services) {
        pre = TB.replace(pre, services, usedSelf,
                         getSelf(),
                         usedParams, getParams());
        return new SymbolicExecDataImpl(baseName, name, forClass, pm,
                                        specifiedIn, modality,
                                        TB.or(origPre, pre), origMby, origMod,
                                        hasRealModifiesClause,
                                        origSelf, origParams, origResult,
                                        origExc, origToBeSaved, id);
    }


    @Override
    public String getHTMLText(Services services) {
        return "<html>"
               + getHTMLBody(services)
               + "</html>";
    }


    protected String getHTMLBody(Services services) {
        return getHTMLSignature()
               + getHTMLFor(origPre, "pre", services)
               + getHTMLFor(origMod, "mod", services)
               + (hasRealModifiesClause ? "" : "<b>, creates no new objects</b>")
               + getHTMLFor(origMby, "measured-by", services)
               + "<br><b>termination</b> " + getModality();
    }


    protected String getHTMLSignature() {
        return "<i>" + LogicPrinter.escapeHTML(getHTMLSignatureBody().toString(),
                                               false) + "</i>";
    }


    protected StringBuffer getHTMLSignatureBody() {
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


    @Override
    public String toString() {
        return name + ":: kjt: " + forClass + "; pm: " + pm + "; modality: "
               + modality + "; pre: " + origPre + "; mby: " + origMby
               + "; mod: " + origMod + "; selfVar: " + origSelf
               + "; paramVars: " + origParams + "; id:" + id;
    }


    @Override
    public String proofToString(Services services) {
        assert false;
        return null;
    }


    @Override
    public ProofOblInput createProofObl(InitConfig initConfig) {
        return new SymbolicExecutionPO(initConfig, this);
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
    public VisibilityModifier getVisibility() {
        assert false; // this is currently not applicable for contracts
        return null;
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
    public Term getResult() {
        return origResult;
    }
    

    @Override
    public ImmutableList<Term> getParams() {
        return origParams;
    }
    
    
    @Override
    public Term getExc() {
        return origExc;
    }
    

    @Override
    public boolean isReadOnlyContract() {
        return origMod.toString().equals("empty");
    }


    @Override
    public boolean toBeSaved() {
	return origToBeSaved;
    }
    
    
    @Override
    public Modality getModality() {
        return modality;
    }


    @Override
    public Modality getPOModality() {
        return poModality;
    }


    @Override
    public SymbolicExecData addMby(Term condition,
                                    Term mby) {
        // bugfix (MU)
        // if the first or the other contract do not have a
        // measured-by-clause, assume no clause at all 
        if (mby == null || origMby == null) {
            return new SymbolicExecDataImpl(baseName, name, forClass, pm,
                                            specifiedIn, modality,
                                            origPre, null, origMod,
                                            hasRealModifiesClause,
                                            origSelf, origParams, origResult,
                                            origExc, origToBeSaved, id);
        } else {
            return new SymbolicExecDataImpl(baseName, name, forClass, pm,
                                            specifiedIn, modality, origPre,
                                            TB.ife(condition, mby, origMby),
                                            origMod, hasRealModifiesClause,
                                            origSelf,
                                            origParams, origResult, origExc,
                                            origToBeSaved, id);
        }
    }


    @Override
    public SymbolicExecData addMod(Term mod,
                                    Services services) {
        Term combinedMod = origMod == null
                           ? mod
                           : (mod == null
                              ? origMod
                              : TB.union(services, origMod, mod));
        return new SymbolicExecDataImpl(baseName, name, forClass, pm,
                                        specifiedIn, modality, origPre, origMby,
                                        combinedMod, hasRealModifiesClause,
                                        origSelf,
                                        origParams, origResult, origExc,
                                        origToBeSaved, id);
    }


    @Override
    public SymbolicExecData setName(String name) {
        return new SymbolicExecDataImpl(baseName, name, forClass, pm,
                                        specifiedIn, modality, origPre, origMby,
                                        origMod, hasRealModifiesClause,
                                        origSelf, origParams,
                                        origResult, origExc,
                                        origToBeSaved, id);
    }


    @Override
    public SymbolicExecData setModality(Modality modality) {
        return new SymbolicExecDataImpl(baseName, name, forClass, pm,
                                        specifiedIn, modality, origPre, origMby,
                                        origMod, hasRealModifiesClause,
                                        origSelf, origParams,
                                        origResult, origExc,
                                        origToBeSaved, id);
    }


    @Override
    public SymbolicExecData setModifies(Term modifies) {
        return new SymbolicExecDataImpl(baseName, name, forClass, pm,
                                        specifiedIn, modality, origPre, origMby,
                                        modifies, hasRealModifiesClause,
                                        origSelf, origParams,
                                        origResult, origExc,
                                        origToBeSaved, id);
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
    public Term getMby() {
        return origMby;
    }


    @Override
    public boolean equals(Contract c) {
        if (c == null || !(c instanceof SymbolicExecData)) {
            return false;
        }
        assert name != null;
        assert forClass != null;
        assert pm != null;
        assert modality != null;
        assert origPre != null;
        assert origMod != null;
        assert origParams != null;
        SymbolicExecData opc = (SymbolicExecData) c;
        return name.equals(opc.getName())
               && forClass.equals(opc.getKJT())
               && pm.equals(opc.getTarget())
               && modality.equals(opc.getModality())
               && origPre.equals(opc.getPre())
               && (origMby != null
                   ? origMby.equals(opc.getMby())
                   : opc.getMby() == null)
               && origMod.equals(opc.getMod())
               && (origSelf != null
                   ? origSelf.equals(opc.getSelf())
                   : opc.getSelf() == null)
               && origParams.equals(opc.getParams())
               && (origResult != null
                   ? getResult().equals(opc.getResult())
                   : opc.getResult() == null)
               && origExc.equals(opc.getExc())
               && id == opc.id()
               && origToBeSaved == opc.toBeSaved();
    }


    @Override
    public Term getMod() {
        return origMod;
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
    public boolean equalsData(SymbolicExecData data) {
        return getKJT().equals(data.getKJT())
                && getTarget().equals(data.getTarget())
                && getModality().equals(data.getModality())
                && getPre().equals(data.getPre())
                && (getMby() != null
                    ? getMby().equals(data.getMby())
                    : data.getMby() == null)
                && getMod().equals(data.getMod())
                && (getSelf() != null
                    ? getSelf().equals(data.getSelf())
                    : data.getSelf() == null)
                && getParams().equals(data.getParams())
                && (getResult() != null
                    ? getResult().equals(data.getResult())
                    : data.getResult() == null)
                && getExc().equals(data.getExc())
                && toBeSaved() == data.toBeSaved();
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
    public ImmutableList<Contract> getContractsToBeStartedBefore(Services services) {
        return ImmutableSLList.<Contract>nil();
    }
    
    
    // the following code is legacy code
    
    @Override
    @Deprecated
    public Term getPre(LocationVariable heap,
                       ProgramVariable selfVar,
                       ImmutableList<ProgramVariable> paramVars,
                       Map<LocationVariable, ? extends ProgramVariable> atPreVars,
                       Services services) {
        throw new UnsupportedOperationException("Not supported any more.");
    }

    @Override
    @Deprecated
    public Term getPre(List<LocationVariable> heapContext,
                       ProgramVariable selfVar,
                       ImmutableList<ProgramVariable> paramVars,
                       Map<LocationVariable, ? extends ProgramVariable> atPreVars,
                       Services services) {
        throw new UnsupportedOperationException("Not supported any more.");
    }

    @Override
    public Term getPre(LocationVariable heap,
                       Term heapTerm,
                       Term selfTerm,
                       ImmutableList<Term> paramTerms,
                       Map<LocationVariable, Term> atPres,
                       Services services) {
        return getPre(heapTerm, selfTerm, paramTerms, services);
    }

    @Override
    @Deprecated
    public Term getPre(List<LocationVariable> heapContext,
                       Map<LocationVariable, Term> heapTerms,
                       Term selfTerm,
                       ImmutableList<Term> paramTerms,
                       Map<LocationVariable, Term> atPres,
                       Services services) {
        throw new UnsupportedOperationException("Not supported any more.");
    }

    @Override
    @Deprecated
    public Term getMby(ProgramVariable selfVar,
                       ImmutableList<ProgramVariable> paramVars,
                       Services services) {
        throw new UnsupportedOperationException("Not supported any more.");
    }

}
