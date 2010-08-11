// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.jmltest;

import javax.swing.JOptionPane;

import de.uka.ilkd.key.gui.*;
import de.uka.ilkd.key.proof.ProofEvent;
import de.uka.ilkd.key.proof.init.proofobligation.SpecExtPO;
import de.uka.ilkd.key.strategy.StrategyProperties;

/**
 * This class is the first step of the jml-wrapper-creation. It calls the
 * Interactiveprover two times. First to try to create a bunch of branches to
 * get many paths which is similar to getting much information about the interna
 * of a program. In the second call the prover settings are changed to try to
 * get a secific structure of the open goals and to try to close infeasible
 * paths. After this steps a new thread of WrapperCreator is created an started.
 * At the end, the prover setting were set back.
 * 
 * @author mbender@uni-koblenz.de
 * 
 */
public class JMLTestFileCreator {

    private final AutoModeListener aml;

    private final KeYMediator medi;

    private final InteractiveProver iProver;

    private String oldMethodProp;

    private String oldLoopProp;

    private int steps;

    /**
     * Creates a new JMLTestFileCreator for the Proof proof
     */
    public JMLTestFileCreator() {
        medi = Main.getInstance().mediator();
        iProver = medi.getInteractiveProver();
        aml = new MyAutoModeListener(this);
        oldLoopProp = null;
        oldMethodProp = null;

    }

    /**
     * This method does the main job. If not in JMLWrapper mode (po not
     * instanceof SpecExtPo) then print a Dialog. Else call the prover, change
     * the setting, call the prover with new settings and then start Creation of
     * the Wrapper file
     * 
     */
    public final void createWrapper() {

        if (medi.getSelectedProof().getPO() instanceof SpecExtPO) {

            iProver.addAutoModeListener(aml);

            iProver.startAutoMode();
        } else {
            JOptionPane
                    .showMessageDialog(
                            Main.getInstance(),
                            "Please choos the <SpecificationExtraction>-PO if you want to use this feature.",
                            "Wrong Proof Obligation chosen!",
                            JOptionPane.WARNING_MESSAGE);

        }

    }

    /**
     * Saves old proof settings an switches to METHOD_NONE and LOOP_NONE
     */
    private final void setProperties() {
        // Save max step an set steps to oldNumber times 5
        steps = medi.getMaxAutomaticSteps();
        medi.setMaxAutomaticSteps(steps * 5);

        // Save old method-handling property, set new to NONE
        if (JRadioButtonHashMap.getButton(StrategyProperties.METHOD_EXPAND)
                .isSelected()) {
            oldMethodProp = StrategyProperties.METHOD_EXPAND;
        } else if (JRadioButtonHashMap.getButton(
                StrategyProperties.METHOD_CONTRACT).isSelected()) {
            oldMethodProp = StrategyProperties.METHOD_CONTRACT;
        } else if (JRadioButtonHashMap
                .getButton(StrategyProperties.METHOD_NONE).isSelected()) {
            oldMethodProp = StrategyProperties.METHOD_NONE;
        }
        JRadioButtonHashMap.getButton(StrategyProperties.METHOD_NONE).doClick();

        // Save old loop-handling property, set new to NONE
        if (JRadioButtonHashMap.getButton(StrategyProperties.LOOP_EXPAND)
                .isSelected()) {
            oldLoopProp = StrategyProperties.LOOP_EXPAND;
        } else if (JRadioButtonHashMap.getButton(
                StrategyProperties.LOOP_INVARIANT).isSelected()) {
            oldLoopProp = StrategyProperties.LOOP_INVARIANT;
        } else if (JRadioButtonHashMap.getButton(StrategyProperties.LOOP_NONE)
                .isSelected()) {
            oldLoopProp = StrategyProperties.LOOP_NONE;
        }
        JRadioButtonHashMap.getButton(StrategyProperties.LOOP_NONE).doClick();
    }

    /**
     * Resets the properties for loop- and method-handling to original values.
     * Removes the AutoModeListener from InteractiveProver
     * 
     */
    public final void resetProperties() {

        if (oldMethodProp != null) {
            JRadioButtonHashMap.getButton(oldMethodProp).doClick();
        }

        if (oldLoopProp != null) {
            JRadioButtonHashMap.getButton(oldLoopProp).doClick();
        }
        medi.setMaxAutomaticSteps(steps);
        iProver.removeAutoModeListener(aml);

    }

    /**
     * Just an AutoModeListener needed for internal use
     */
    private final class MyAutoModeListener implements AutoModeListener {

        private final JMLTestFileCreator jmltfc;

        private MyAutoModeListener(JMLTestFileCreator jmltfc) {
            this.jmltfc = jmltfc;
        }

        public void autoModeStarted(ProofEvent e) {
        }

        /**
         * After first run off Prover is finished, change setting and start
         * prover again. After second iteration is finished start creation of
         * wrapper file
         * 
         * @see de.uka.ilkd.key.gui.AutoModeListener#autoModeStopped(de.uka.ilkd.key.proof.ProofEvent)
         */
        public void autoModeStopped(ProofEvent e) {
            if ((oldLoopProp == null) && (oldMethodProp == null)) {
                setProperties();
                medi.getInteractiveProver().startAutoMode();
            } else {
                final WrapperConstructor wc = new WrapperConstructor(jmltfc,
                        medi.getSelectedProof());
                wc.start();
            }

        }
    }

}
