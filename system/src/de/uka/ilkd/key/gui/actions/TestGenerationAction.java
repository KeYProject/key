package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;

import javax.swing.Icon;

import de.uka.ilkd.key.gui.AutoModeListener;
import de.uka.ilkd.key.gui.IconFactory;
import de.uka.ilkd.key.gui.KeYSelectionEvent;
import de.uka.ilkd.key.gui.KeYSelectionListener;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.testgen.TGInfoDialog;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofEvent;


/**
 * Action which generates test cases for all open nodes. If the proof is closed,
 * test cases will be generated for nodes on which the emptyModality rule was
 * applied.
 * 
 * @author mihai
 * 
 */
@SuppressWarnings("serial")
public class TestGenerationAction extends MainWindowAction {
	
	private static final String NAME = "Generate Testcases";
	private static final String TOOLTIP = "Generate test cases for open goals";
	
	//public static Proof originalProof;

	public TestGenerationAction(MainWindow mainWindow) {
		super(mainWindow);
		setName(TestGenerationAction.NAME);
		setTooltip(TestGenerationAction.TOOLTIP);
		Icon icon = IconFactory.testGeneration(MainWindow.TOOLBAR_ICON_SIZE);
        putValue(SMALL_ICON, icon);
		init();
	}

	@Override
	public void actionPerformed(ActionEvent e) {
		new TGInfoDialog();
	}

	

	/**
	 * Registers the action at some listeners to update its status in a correct
	 * fashion. This method has to be invoked after the Main class has been
	 * initialised with the KeYMediator.
	 */
	public void init() {
		final KeYSelectionListener selListener = new KeYSelectionListener() {
			@Override
			public void selectedNodeChanged(KeYSelectionEvent e) {
				final Proof proof = getMediator().getSelectedProof();
				if (proof == null) {
					// no proof loaded
					setEnabled(false);
				} else {
					setEnabled(true);
				}
			}

			@Override
			public void selectedProofChanged(KeYSelectionEvent e) {
				selectedNodeChanged(e);
			}
		};
		getMediator().addKeYSelectionListener(selListener);
		getMediator().addAutoModeListener(new AutoModeListener() {
			@Override
			public void autoModeStarted(ProofEvent e) {
				getMediator().removeKeYSelectionListener(selListener);
				setEnabled(false);
			}

			@Override
			public void autoModeStopped(ProofEvent e) {
				getMediator().addKeYSelectionListener(selListener);
				// selListener.selectedNodeChanged(null);
			}
		});
		selListener.selectedNodeChanged(new KeYSelectionEvent(getMediator()
		        .getSelectionModel()));
	}
}
