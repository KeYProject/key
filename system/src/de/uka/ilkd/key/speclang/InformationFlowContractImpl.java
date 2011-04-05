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
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.proof.OpReplacer;
import de.uka.ilkd.key.proof.init.InformationFlowContractPO;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.util.LinkedHashMap;

/**
 * Standard implementation of the DependencyContract interface.
 */
public final class InformationFlowContractImpl
        implements InformationFlowContract {

    private static final TermBuilder TB = TermBuilder.DF;
    private final String baseName;
    private final String name;
    private final KeYJavaType kjt;
    private final ProgramMethod pm;
    private final Term originalPre;
    private final Term originalMby;
    private final Term originalDep;
    private final Term originalMod;
    private final Term originalSaveFor;
    private final Term originalDeclassify;
    private final ProgramVariable originalSelfVar;
    private final ImmutableList<ProgramVariable> originalParamVars;
    private final int id;

    //-------------------------------------------------------------------------
    //constructors
    //-------------------------------------------------------------------------
    private InformationFlowContractImpl(String baseName,
                                        String name,
                                        KeYJavaType kjt,
                                        ProgramMethod pm,
                                        Term pre,
                                        Term mby,
                                        Term dep,
                                        Term mod,
                                        Term saveFor,
                                        Term declassify,
                                        ProgramVariable selfVar,
                                        ImmutableList<ProgramVariable> paramVars,
                                        int id) {
        assert baseName != null;
        assert kjt != null;
        assert pm != null;
        assert pre != null;
//	assert dep != null;
        assert mod != null;
//	assert saveFor != null;
//	assert declassify != null;
        assert (selfVar == null) == pm.isStatic();
        assert paramVars != null;
        assert paramVars.size() == pm.arity() - (pm.isStatic() ? 1 : 2);
        this.baseName = baseName;
        this.name = generateName(name, baseName, kjt, pm, id);
        this.kjt = kjt;
        this.pm = pm;
        this.originalPre = pre;
        this.originalMby = mby;
        this.originalDep = dep;
        this.originalMod = mod;
        this.originalSaveFor = saveFor;
        this.originalDeclassify = declassify;
        this.originalSelfVar = selfVar;
        this.originalParamVars = paramVars;
        this.id = id;
    }

    public InformationFlowContractImpl(String baseName,
                                       KeYJavaType kjt,
                                       ProgramMethod pm,
                                       Term pre,
                                       Term mby,
                                       Term dep,
                                       Term mod,
                                       Term saveFor,
                                       Term declassify,
                                       ProgramVariable selfVar,
                                       ImmutableList<ProgramVariable> paramVars) {
        this(baseName, null, kjt, pm, pre, mby, dep, mod, saveFor,
             declassify, selfVar, paramVars, INVALID_ID);
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
        return kjt;
    }

    @Override
    public ProgramMethod getTarget() {
        return pm;
    }

    @Override
    public boolean hasMby() {
        return originalMby != null;
    }

    @Override
    public Term getPre(ProgramVariable selfVar,
                       ImmutableList<ProgramVariable> paramVars,
                       Services services) {
        assert (selfVar == null) == (originalSelfVar == null);
        assert paramVars != null;
        assert paramVars.size() == originalParamVars.size();
        assert services != null;
        OpReplacer or = generateOperationReplacer(selfVar, paramVars);
        return or.replace(originalPre);
    }

    @Override
    public Term getPre(Term heapTerm,
                       Term selfTerm,
                       ImmutableList<Term> paramTerms,
                       Services services) {
        assert heapTerm != null;
        assert (selfTerm == null) == (originalSelfVar == null);
        assert paramTerms != null;
        assert paramTerms.size() == originalParamVars.size();
        assert services != null;
        OpReplacer or = generateOperationReplacer(heapTerm, selfTerm,
                                                  paramTerms, services);
        return or.replace(originalPre);
    }

    @Override
    public Term getMby(ProgramVariable selfVar,
                       ImmutableList<ProgramVariable> paramVars,
                       Services services) {
        assert hasMby();
        assert (selfVar == null) == (originalSelfVar == null);
        assert paramVars != null;
        assert paramVars.size() == originalParamVars.size();
        assert services != null;
        OpReplacer or = generateOperationReplacer(selfVar, paramVars);
        return or.replace(originalMby);
    }

    @Override
    public Term getMby(Term heapTerm,
                       Term selfTerm,
                       ImmutableList<Term> paramTerms,
                       Services services) {
        assert hasMby();
        assert heapTerm != null;
        assert (selfTerm == null) == (originalSelfVar == null);
        assert paramTerms != null;
        assert paramTerms.size() == originalParamVars.size();
        assert services != null;
        OpReplacer or = generateOperationReplacer(heapTerm, selfTerm,
                                                  paramTerms, services);
        return or.replace(originalMby);
    }

    @Override
    public Term getDep(ProgramVariable selfVar,
                       ImmutableList<ProgramVariable> paramVars,
                       Services services) {
        assert (selfVar == null) == (originalSelfVar == null);
        assert paramVars != null;
        assert paramVars.size() == originalParamVars.size();
        assert services != null;
        OpReplacer or = generateOperationReplacer(selfVar, paramVars);
        return or.replace(originalDep);
    }

    @Override
    public Term getDep(Term heapTerm,
                       Term selfTerm,
                       ImmutableList<Term> paramTerms,
                       Services services) {
        assert heapTerm != null;
        assert (selfTerm == null) == (originalSelfVar == null);
        assert paramTerms != null;
        assert paramTerms.size() == originalParamVars.size();
        assert services != null;
        OpReplacer or = generateOperationReplacer(heapTerm, selfTerm,
                                                  paramTerms, services);
        return or.replace(originalDep);
    }

    @Override
    public Term getMod(ProgramVariable selfVar,
                       ImmutableList<ProgramVariable> paramVars,
                       Services services) {
        assert (selfVar == null) == (originalSelfVar == null);
        assert paramVars != null;
        assert paramVars.size() == originalParamVars.size();
        assert services != null;
        OpReplacer or = generateOperationReplacer(selfVar, paramVars);
        return or.replace(originalMod);
    }

    @Override
    public Term getMod(Term heapTerm,
                       Term selfTerm,
                       ImmutableList<Term> paramTerms,
                       Services services) {
        assert heapTerm != null;
        assert (selfTerm == null) == (originalSelfVar == null);
        assert paramTerms != null;
        assert paramTerms.size() == originalParamVars.size();
        assert services != null;
        OpReplacer or = generateOperationReplacer(heapTerm, selfTerm,
                                                  paramTerms, services);
        return or.replace(originalMod);
    }

    @Override
    public Term getSaveFor(ProgramVariable selfVar,
                           ImmutableList<ProgramVariable> paramVars,
                           Services services) {
        assert (selfVar == null) == (originalSelfVar == null);
        assert paramVars != null;
        assert paramVars.size() == originalParamVars.size();
        assert services != null;
        OpReplacer or = generateOperationReplacer(selfVar, paramVars);
        return or.replace(originalSaveFor);
    }

    @Override
    public Term getSaveFor(Term heapTerm,
                           Term selfTerm,
                           ImmutableList<Term> paramTerms,
                           Services services) {
        assert heapTerm != null;
        assert (selfTerm == null) == (originalSelfVar == null);
        assert paramTerms != null;
        assert paramTerms.size() == originalParamVars.size();
        assert services != null;
        OpReplacer or = generateOperationReplacer(heapTerm, selfTerm,
                                                  paramTerms, services);
        return or.replace(originalSaveFor);
    }

    @Override
    public Term getDeclassify(ProgramVariable selfVar,
                              ImmutableList<ProgramVariable> paramVars,
                              Services services) {
        assert (selfVar == null) == (originalSelfVar == null);
        assert paramVars != null;
        assert paramVars.size() == originalParamVars.size();
        assert services != null;
        OpReplacer or = generateOperationReplacer(selfVar, paramVars);
        return or.replace(originalDeclassify);
    }

    @Override
    public Term getDeclassify(Term heapTerm,
                              Term selfTerm,
                              ImmutableList<Term> paramTerms,
                              Services services) {
        assert heapTerm != null;
        assert (selfTerm == null) == (originalSelfVar == null);
        assert paramTerms != null;
        assert paramTerms.size() == originalParamVars.size();
        assert services != null;
        OpReplacer or = generateOperationReplacer(heapTerm, selfTerm,
                                                  paramTerms, services);
        return or.replace(originalDeclassify);
    }

    @Override
    public InformationFlowContract setID(int newId) {
        return new InformationFlowContractImpl(baseName, null, kjt, pm,
                                               originalPre, originalMby,
                                               originalDep, originalMod,
                                               originalSaveFor,
                                               originalDeclassify,
                                               originalSelfVar,
                                               originalParamVars, newId);
    }

    @Override
    public InformationFlowContract setTarget(KeYJavaType newKJT,
                                             ObserverFunction newPM,
                                             Services services) {
        return new InformationFlowContractImpl(baseName, null, newKJT,
                                               (ProgramMethod) newPM,
                                               originalPre, originalMby,
                                               originalDep, originalMod,
                                               originalSaveFor,
                                               originalDeclassify,
                                               originalSelfVar,
                                               originalParamVars, id);
    }

    @Override
    public String getHTMLText(Services services) {
        // TODO: Check for correctness!!
        final StringBuffer sig = new StringBuffer();
        if (pm.isConstructor()) {
            sig.append(originalSelfVar);
            sig.append(" = new ");
        }
        if (!pm.isStatic() && !pm.isConstructor()) {
            sig.append(originalSelfVar);
            sig.append(".");
        }
        sig.append(pm.getName());
        sig.append("(");
        for (ProgramVariable pv : originalParamVars) {
            sig.append(pv.name()).append(", ");
        }
        if (!originalParamVars.isEmpty()) {
            sig.setLength(sig.length() - 2);
        }
        sig.append(")");

        final String pre = LogicPrinter.quickPrintTerm(originalPre, services);
        final String mby = hasMby()
                           ? LogicPrinter.quickPrintTerm(originalMby, services)
                           : null;
        final String mod = LogicPrinter.quickPrintTerm(originalMod, services);

        return "<html>"
               + "<i>" + LogicPrinter.escapeHTML(sig.toString(), false) + "</i>"
               + "<br><b>pre</b> "
               + LogicPrinter.escapeHTML(pre, false)
               + "<br><b>mod</b> "
               + LogicPrinter.escapeHTML(mod, false)
               + (hasMby()
                  ? "<br><b>measured-by</b> " + LogicPrinter.escapeHTML(mby,
                                                                        false)
                  : "")
               + "<br><b>termination</b> "
               + "</html>";
    }

    @Override
    public boolean toBeSaved() {
        return false; //because dependency contracts currently cannot be
        //specified directly in DL
    }

    @Override
    public String proofToString(Services services) {
        assert false;
        return null;
    }

    @Override
    public String toString() {
        // TODO: all fields should be printed!!
        return "pre: " + originalPre
               + "; mby: " + originalMby
               + "; mod: " + originalMod;
    }

    private String generateName(String myName,
                                String myBaseName,
                                KeYJavaType myKjt,
                                ProgramMethod myPm,
                                int myId) {
        return myName != null ? myName : myBaseName
                                         + " [id: "
                                         + myId
                                         + " / "
                                         + myPm
                                         + (myKjt.equals(myPm.getContainerType())
                                            ? ""
                                            : " for "
                                              + myKjt.getJavaType().getName())
                                         + "]";
    }

    private OpReplacer generateOperationReplacer(ProgramVariable selfVar,
                                                 ImmutableList<ProgramVariable> paramVars) {
        LinkedHashMap<ProgramVariable, ProgramVariable> map =
                new LinkedHashMap<ProgramVariable, ProgramVariable>();
        map.put(originalSelfVar, selfVar);
        map.putAll(originalParamVars, paramVars);
        OpReplacer or = new OpReplacer(map);
        return or;
    }

    private OpReplacer generateOperationReplacer(Term heapTerm,
                                                 Term selfTerm,
                                                 ImmutableList<Term> paramTerms,
                                                 Services services) {
        LinkedHashMap<Term, Term> map = new LinkedHashMap<Term, Term>();
        map.put(TB.heap(services), heapTerm);
        map.put(TB.var(originalSelfVar), selfTerm);
        ImmutableList<Term> originalParamTerms = TB.var(originalParamVars);
        map.putAll(originalParamTerms, paramTerms);
        OpReplacer or = new OpReplacer(map);
        return or;
    }

    @Override
    public ProofOblInput createProofObl(InitConfig initConfig,
                                        Contract contract) {
        return new InformationFlowContractPO(initConfig,
                                             (InformationFlowContract) contract);
    }
}
