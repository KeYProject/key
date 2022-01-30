// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.settings;


import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.smt.SMTSettings;
import de.uka.ilkd.key.smt.st.SolverType;
import de.uka.ilkd.key.taclettranslation.assumptions.SupportedTaclets;

import java.beans.PropertyChangeListener;
import java.io.File;
import java.util.Collection;
import java.util.LinkedList;

/**
 * The default implementation of {@link SMTSettings}.
 */
public class DefaultSMTSettings implements SMTSettings {
    private final ProofDependentSMTSettings pdSettings;
    private final ProofIndependentSMTSettings piSettings;
    private final Proof proof;
    private LinkedList<Taclet> taclets = null;
    private final NewSMTTranslationSettings newTranslationSettings;


    public DefaultSMTSettings(ProofDependentSMTSettings pdSettings,
                              ProofIndependentSMTSettings piSettings,
                              NewSMTTranslationSettings newTransSettings,
                              Proof proof) {
        super();
        this.pdSettings = pdSettings;
        this.piSettings = piSettings;
        this.newTranslationSettings = newTransSettings;
        this.proof = proof;

    }

    public void copy(DefaultSMTSettings settings) {
        pdSettings.copy(settings.pdSettings);
        piSettings.copy(settings.piSettings);
        newTranslationSettings.copy(settings.newTranslationSettings);
        taclets = settings.taclets;
    }

    public ProofDependentSMTSettings getPdSettings() {
        return pdSettings;
    }

    public ProofIndependentSMTSettings getPiSettings() {
        return piSettings;
    }

    public Proof getProof() {
        return proof;
    }


    @Override
    public int getMaxConcurrentProcesses() {

        return piSettings.getMaxConcurrentProcesses();
    }

    @Override
    public int getMaxNumberOfGenerics() {

        return pdSettings.getMaxGenericSorts();
    }

    @Override
    public String getSMTTemporaryFolder() {
        return PathConfig.getKeyConfigDir()
                + File.separator + "smt_formula";
    }

    @Override
    public Collection<Taclet> getTaclets() {
        if (taclets == null) {
            taclets = new LinkedList<>();
            if (proof == null) {
                return taclets;
            }

            for (Taclet taclet : proof.getInitConfig().activatedTaclets()) {
                if (pdSettings.getSupportedTaclets().contains(taclet.name().toString(), true)) {
                    taclets.add(taclet);
                }
            }
        }
        return taclets;
    }

    @Override
    public long getTimeout() {
        return piSettings.getTimeout();
    }

    @Override
    public long getTimeout(SolverType type) {
        ProofIndependentSMTSettings.SolverData data = piSettings.getSolverData(type);
        if (data != null && data.getTimeout() >= 1) {
            return data.getTimeout();
        }
        return getTimeout();
    }


    @Override
    public boolean instantiateNullAssumption() {

        return pdSettings.isUseNullInstantiation();
    }

    @Override
    public boolean makesUseOfTaclets() {

        return !getTaclets().isEmpty();

    }


    @Override
    public boolean useAssumptionsForBigSmallIntegers() {

        return pdSettings.isUseConstantsForIntegers();
    }

    @Override
    public boolean useBuiltInUniqueness() {

        return pdSettings.isUseBuiltInUniqueness();
    }

    @Override
    public boolean useExplicitTypeHierarchy() {

        return pdSettings.isUseExplicitTypeHierarchy();
    }

    @Override
    public boolean useUninterpretedMultiplicationIfNecessary() {

        return pdSettings.isUseUIMultiplication();
    }

    public SupportedTaclets getSupportedTaclets() {
        return pdSettings.getSupportedTaclets();
    }

    public ProofIndependentSMTSettings.ProgressMode getModeOfProgressDialog() {
        return piSettings.getModeOfProgressDialog();
    }

    public boolean storeSMTTranslationToFile() {
        return piSettings.isStoreSMTTranslationToFile();
    }

    public boolean storeTacletTranslationToFile() {
        return piSettings.isStoreTacletTranslationToFile();
    }

    public String getPathForTacletTranslation() {
        return piSettings.getPathForTacletTranslation();
    }

    public String getPathForSMTTranslation() {
        return piSettings.getPathForSMTTranslation();
    }

    public void addListener(PropertyChangeListener listener) {
        piSettings.addPropertyChangeListener(listener);
        pdSettings.addPropertyChangeListener(listener);
    }

    @Override
    public long getMaximumInteger() {
        return pdSettings.getMaxInteger();
    }

    @Override
    public long getMinimumInteger() {
        return pdSettings.getMinInteger();
    }

    @Override
    public String getLogic() {
        return "AUFLIA";
    }

    @Override
    public boolean checkForSupport() {
        return piSettings.isCheckForSupport();
    }

    @Override
    public long getIntBound() {
        return piSettings.getIntBound();
    }

    @Override
    public long getHeapBound() {
        return piSettings.getHeapBound();
    }

    @Override
    public long getSeqBound() {
        return piSettings.getSeqBound();
    }

    @Override
    public long getObjectBound() {
        return piSettings.getObjectBound();
    }

    @Override
    public long getLocSetBound() {
        return piSettings.getLocsetBound();
    }

    @Override
    public boolean invarianForall() {
        return pdSettings.isInvariantForall();
    }

    @Override
    public NewSMTTranslationSettings getNewSettings() {
        return newTranslationSettings;
    }


    public NewSMTTranslationSettings getNewTranslationSettings() {
        return newTranslationSettings;
    }


}
