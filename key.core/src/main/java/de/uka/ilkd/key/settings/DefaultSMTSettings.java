/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.settings;


import java.beans.PropertyChangeListener;
import java.io.File;
import java.util.Collection;
import java.util.LinkedList;

import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.smt.SMTSettings;
import de.uka.ilkd.key.smt.solvertypes.SolverType;
import de.uka.ilkd.key.taclettranslation.assumptions.SupportedTaclets;

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
            ProofIndependentSMTSettings piSettings, NewSMTTranslationSettings newTransSettings,
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
        return PathConfig.getKeyConfigDir() + File.separator + "smt_formula";
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
        if (piSettings.getSolverTimeout(type) >= 1) {
            return piSettings.getSolverTimeout(type);
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
        // Set the logic to the most general one according to the SMT-LIB standard.
        return "AUFNIRA";
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
