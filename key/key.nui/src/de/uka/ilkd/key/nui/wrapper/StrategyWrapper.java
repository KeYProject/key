package de.uka.ilkd.key.nui.wrapper;

import javax.swing.Box;
import javax.swing.JScrollPane;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.StrategySelectionView;
import de.uka.ilkd.key.gui.actions.AutoModeAction;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.strategy.Strategy;
import javafx.embed.swing.SwingNode;

/**
 * Creates the StrategySelectionView component (Swing component) and wraps it
 * into a JavaFX component.
 * 
 * @author Patrick Jattke
 * @author Florian Breitfelder
 */
@SuppressWarnings("PMD.AtLeastOneConstructor")
//PMD will also complain if adding the constructor, then saying "avoid useless constructors"
public class StrategyWrapper extends BasicWrapper {

    /**
     * Stores the StrategySelectionView.
     */
    private StrategySelectionView ssv;

    /**
     * Stores the AutoModeAction associated to the StrategySelectionView.
     */
    private AutoModeAction ama;

    /**
     * Refreshes the components on the StrategySelectionView after a new proof
     * file was loaded.
     * 
     * @param proof
     *            The loaded proof file.
     */
    public void refreshComponents(final Proof proof) {
        ssv.refresh(proof);
        ama.enable();
    }

    /**
     * Creates a new StrategyComponent and returns the resulting FX SwingNode.
     * 
     * @param proof
     *            The proof file which should be associated with the
     *            StrategyComponent.
     * 
     * @return {@link SwingNode} The SwingNode which can be attached to the FX
     *         SceneGraph.
     * 
     */
    public SwingNode createStrategyComponent(final Proof proof) {
        final MainWindow mainWindow = MainWindow.getInstance();
        mainWindow.setVisible(false);

        ama = new AutoModeAction(mainWindow);

        ssv = new StrategySelectionView(ama);
        JavaProfile.getDefaultInstance();

        if (proof != null) {
            mainWindow.getMediator().getSelectionModel().setProof(proof);
        }

        ssv.setMediator(mainWindow.getMediator());

        ssv.setMediator(mainWindow.getMediator());
        ssv.setEnabled(true);
        if (proof != null) {
            ssv.setEnabled(false);
            ssv.refresh(proof);
        }

        final Box box = (Box) ssv.getComponent(0);
        final JScrollPane scrollPane = (JScrollPane) box.getComponent(5);

        ssv.removeAll();
        ssv.add(scrollPane);

        return super.addSwingComponent(ssv);
    }

    /**
     * Returns the strategy of the currently loaded proof.
     * 
     * @return {@link Strategy} of the currently loaded proof.
     */
    public Strategy getStrategy() {
        final MainWindow mainWindow = MainWindow.getInstance();
        return mainWindow.getMediator().getSelectionModel().getSelectedProof()
                .getActiveStrategy();
    }

    /**
     * Getter.
     * @return the {@link StrategySelectionView}.
     */
    public StrategySelectionView getSsv() {
        return ssv;
    }
    /**
     * Setter.
     * @param ssv the {@link StrategySelectionView} you want to set.
     */
    public void setSsv(final StrategySelectionView ssv) {
        this.ssv = ssv;
    }
    /**
     * Getter.
     * @return the {@link AutoModeAction}.
     */
    public AutoModeAction getAma() {
        return ama;
    }
    /**
     * Setter.
     * @param ama the {@link AutoModeAction} you want to set.
     */
    public void setAma(final AutoModeAction ama) {
        this.ama = ama;
    }

}
