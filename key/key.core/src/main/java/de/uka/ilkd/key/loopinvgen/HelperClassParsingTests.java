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

/*
 * Created on 18.12.2004
 */
package de.uka.ilkd.key.loopinvgen;

import java.io.File;

import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.proof.init.KeYUserProblemFile;
import de.uka.ilkd.key.proof.init.ProblemInitializer;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.rule.OneStepSimplifier;
import de.uka.ilkd.key.settings.ProofSettings;
import de.uka.ilkd.key.strategy.Strategy;
import de.uka.ilkd.key.strategy.StrategyProperties;

public class HelperClassParsingTests {
    private static final Profile profile = JavaProfile.getDefaultProfile(); //{
    public HelperClassParsingTests() {

    }

    public ProofAggregate parse(File file) {
        return parse(file, profile);
    }

    public ProofAggregate parse(File file, Profile profile) {
        ProblemInitializer pi = null;
        ProofAggregate result = null;

        try {
            KeYUserProblemFile po
                    = new KeYUserProblemFile("UpdatetermTest", file, null, profile);
            pi = new ProblemInitializer(profile);

            result = pi.startProver(po, po);

        } catch (Exception e) {
//            System.err.println("Exception occurred while parsing "+file+"\n");
            e.printStackTrace();
            System.exit(-1);
        }
        return result;
    }

    public ProofAggregate parseThrowException(File file) throws ProofInputException{
        return parseThrowException(file, profile);
    }


    public ProofAggregate parseThrowException(File file, Profile profile) throws ProofInputException{
        KeYUserProblemFile po
                = new KeYUserProblemFile("UpdatetermTest", file, null, profile);
        ProblemInitializer pi = new ProblemInitializer(profile);
        return pi.startProver(po, po);
    }

    public Term extractProblemTerm(Proof p) {
        return p.root().sequent().succedent().iterator().next().formula();
    }

    /**
     * Checks if one step simplification is enabled in the given {@link Proof}.
     * @param proof The {@link Proof} to read from or {@code null} to return the general settings value.
     * @return {@code true} one step simplification is enabled, {@code false} if disabled.
     */
    public static boolean isOneStepSimplificationEnabled(Proof proof) {
        StrategyProperties props;
        if (proof != null && !proof.isDisposed()) {
            props = proof.getSettings().getStrategySettings().getActiveStrategyProperties();
        }
        else {
            props = ProofSettings.DEFAULT_SETTINGS.getStrategySettings().getActiveStrategyProperties();
        }

        return props.get(StrategyProperties.OSS_OPTIONS_KEY).equals(StrategyProperties.OSS_ON);
    }

    /**
     * Defines if one step simplification is enabled in general and within the
     * {@link Proof}.
     *
     * @param proof
     *            The optional {@link Proof}.
     * @param enabled
     *            {@code true} use one step simplification, {@code false} do not
     *            use one step simplification.
     */
    public static void setOneStepSimplificationEnabled(Proof proof,
                                                       boolean enabled) {
        final String newVal = enabled ? StrategyProperties.OSS_ON
                : StrategyProperties.OSS_OFF;

        {
            final StrategyProperties newProps = ProofSettings.DEFAULT_SETTINGS
                    .getStrategySettings().getActiveStrategyProperties();
            newProps.setProperty(StrategyProperties.OSS_OPTIONS_KEY, newVal);
            ProofSettings.DEFAULT_SETTINGS.getStrategySettings()
                    .setActiveStrategyProperties(newProps);
        }

        if (proof != null && !proof.isDisposed()) {
            final StrategyProperties newProps = proof.getSettings()
                    .getStrategySettings().getActiveStrategyProperties();
            newProps.setProperty(StrategyProperties.OSS_OPTIONS_KEY, newVal);

            Strategy.updateStrategySettings(proof, newProps);
            OneStepSimplifier.refreshOSS(proof);
        }
    }

    public static Services createServices(File keyFile) {
        JavaInfo javaInfo = new HelperClassParsingTests().parse(keyFile)
                .getFirstProof().getJavaInfo();
        return javaInfo.getServices();
    }

}