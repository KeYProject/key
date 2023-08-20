/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.testcase.smt.ce;

import java.io.File;
import java.util.Collection;

import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.settings.NewSMTTranslationSettings;
import de.uka.ilkd.key.settings.PathConfig;
import de.uka.ilkd.key.settings.ProofDependentSMTSettings;
import de.uka.ilkd.key.smt.solvertypes.SolverType;

public class SMTTestSettings implements de.uka.ilkd.key.smt.SMTSettings {


    public long getGlobalBound() {
        return 0;
    }

    @Override
    public int getMaxConcurrentProcesses() {
        return 1;
    }

    @Override
    public int getMaxNumberOfGenerics() {
        return 2;
    }

    @Override
    public String getSMTTemporaryFolder() {
        return PathConfig.getKeyConfigDir() + File.separator + "smt_formula";
    }

    @Override
    public Collection<Taclet> getTaclets() {
        return null;
    }

    @Override
    public long getTimeout() {
        return 300000;
    }

    @Override
    public long getTimeout(SolverType type) {
        return getTimeout();
    }

    @Override
    public boolean instantiateNullAssumption() {
        return true;
    }

    @Override
    public boolean makesUseOfTaclets() {
        return false;
    }

    @Override
    public boolean useExplicitTypeHierarchy() {
        return false;
    }

    @Override
    public boolean useBuiltInUniqueness() {
        return false;
    }

    @Override
    public boolean useAssumptionsForBigSmallIntegers() {
        return false;
    }

    @Override
    public boolean useUninterpretedMultiplicationIfNecessary() {
        return false;
    }

    @Override
    public long getMaximumInteger() {

        return ProofDependentSMTSettings.getDefaultSettingsData().getMaxInteger();
    }

    @Override
    public long getMinimumInteger() {

        return ProofDependentSMTSettings.getDefaultSettingsData().getMinInteger();
    }

    @Override
    public String getLogic() {
        // Set the logic to the most general one according to the SMT-LIB standard.
        return "AUFNIRA";
    }

    @Override
    public boolean checkForSupport() {
        return false;
    }

    @Override
    public long getIntBound() {
        return 3;
    }

    @Override
    public long getHeapBound() {
        return 3;
    }

    @Override
    public long getSeqBound() {
        return 3;
    }

    @Override
    public long getObjectBound() {
        return 3;
    }

    @Override
    public long getLocSetBound() {
        return 3;
    }

    @Override
    public boolean invarianForall() {
        return false;
    }

    @Override
    public NewSMTTranslationSettings getNewSettings() {
        return new NewSMTTranslationSettings();
    }


}
