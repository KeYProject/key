/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.control;

import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;
import de.uka.ilkd.key.speclang.PositionedString;

import org.key_project.util.collection.ImmutableSet;

/**
 * The {@link DefaultUserInterfaceControl} which allows proving in case that no specific user
 * interface is available.
 * <p>
 * In case that no user interface should be used see also {@link KeYEnvironment} which provides
 * static methods to load source code and to instantiate this class.
 *
 * @author Martin Hentschel
 * @see KeYEnvironment
 */
public class DefaultUserInterfaceControl extends AbstractUserInterfaceControl {
    /**
     * The used {@link TermLabelVisibilityManager}.
     */
    private final TermLabelVisibilityManager termLabelVisibilityManager =
        new TermLabelVisibilityManager();

    /**
     * The used {@link DefaultProofControl}.
     */
    private final DefaultProofControl proofControl;

    /**
     * Constructor.
     */
    public DefaultUserInterfaceControl() {
        proofControl = new DefaultProofControl(this, this);
    }

    /**
     * Constructor.
     *
     * @param customization An optional {@link RuleCompletionHandler}.
     */
    public DefaultUserInterfaceControl(RuleCompletionHandler customization) {
        proofControl = new DefaultProofControl(this, this, customization);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public DefaultProofControl getProofControl() {
        return proofControl;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public ProofEnvironment createProofEnvironmentAndRegisterProof(ProofOblInput proofOblInput,
            ProofAggregate proofList, InitConfig initConfig) {
        // TODO: Find out why the proof has to be registered. This method should just return null
        // and do nothing.
        initConfig.getServices().getSpecificationRepository().registerProof(proofOblInput,
            proofList.getFirstProof());

        // This has to be done to prive the proofList with the environment object.
        final ProofEnvironment env = new ProofEnvironment(initConfig);
        env.registerProof(proofOblInput, proofList);
        return env;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean selectProofObligation(InitConfig initConfig) {
        return false;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void progressStarted(Object sender) {
        // Nothing to do
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void progressStopped(Object sender) {
        // Nothing to do
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void reportStatus(Object sender, String status, int progress) {
        // Nothing to do
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void reportStatus(Object sender, String status) {
        // Nothing to do
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void resetStatus(Object sender) {
        // Nothing to do
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void reportException(Object sender, ProofOblInput input, Exception e) {
        // Nothing to do
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void setProgress(int progress) {
        // Nothing to do
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void setMaximum(int maximum) {
        // Nothing to do
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void registerProofAggregate(ProofAggregate pa) {
        // Nothing to do
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void reportWarnings(ImmutableSet<PositionedString> warnings) {
        // Nothing to do
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public TermLabelVisibilityManager getTermLabelVisibilityManager() {
        return termLabelVisibilityManager;
    }
}
