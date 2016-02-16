package de.uka.ilkd.key.nui.wrapper;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.*;
import de.uka.ilkd.key.gui.actions.AutoModeAction;
import de.uka.ilkd.key.proof.Proof;
import javafx.embed.swing.SwingNode;

/**
 * Creates the StrategySelectionView component (Swing component) and wraps it
 * into a JavaFX component.
 * 
 * @author Patrick Jattke
 *
 */
public class StrategyWrapper extends BasicWrapper {

    /**
     * Stores the StrategySelectionView.
     */
    StrategySelectionView ssv;
    /**
     * Stores the AutoModeAction associated to the StrategySelectionView.
     */
    AutoModeAction ama;

    /**
     * Creates a new Strategy Wrapper object.
     */
    public StrategyWrapper() {

    }

    /**
     * Refreshes the components on the StrategySelectionView after a new proof
     * file was loaded.
     * 
     * @param p
     *            The loaded proof file.
     */
    public void refreshComponents(Proof p) {
        ssv.refresh(p);
        ama.enable();
    }

    /**
     * Creates a new StrategyComponent and returns the resulting FX SwingNode.
     * 
     * @return {@link SwingNode} The SwingNode which can be attached to the FX
     *         SceneGraph.
     */
    public SwingNode createStrategyComponent() {
        MainWindow mw = MainWindow.getInstance();
        mw.setVisible(false);
        ama = new AutoModeAction(mw);
        ssv = new StrategySelectionView(ama);
        ssv.setEnabled(true);
        ssv.setMediator(mw.getMediator());
        SwingNode node = super.addSwingComponent(ssv);
        return node;
    }

}
