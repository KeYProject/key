package de.uka.ilkd.key.gui.testgen;

import java.util.List;

import javax.swing.SwingWorker;

import de.uka.ilkd.key.control.UserInterfaceControl;
import de.uka.ilkd.key.core.InterruptListener;
import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.nodeviews.SequentViewInputListener;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.SingleProof;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
import de.uka.ilkd.key.smt.testgen.AbstractTestGenerator;
import de.uka.ilkd.key.smt.testgen.StopRequest;

public class TGWorker extends SwingWorker<Void, Void> implements InterruptListener, StopRequest {
	private final TGInfoDialog tgInfoDialog;
	private boolean stop;
	private final MainWindowTestGenerator testGenerator;
	private Proof originalProof;

	public TGWorker(TGInfoDialog tgInfoDialog){
		this.tgInfoDialog = tgInfoDialog;
		this.originalProof = getMediator().getSelectedProof();
		this.testGenerator = new MainWindowTestGenerator(getMediator(), originalProof, false);
	}
   
   /**
    * Registers created {@link Proof}s in the {@link MainWindow} visible to the user.
    * <p>
    * <b>This class provides only the user interface and no test generation 
    * logic which is implemented by the 
    * {@link AbstractTestGenerator}</b>.
    */
   public static class MainWindowTestGenerator extends AbstractTestGenerator {
      /**
       * Defines if created {@link Proof}s are visible in the {@link MainWindow} or not.
       */
      private final boolean showInMainWindow;
      
      private final KeYMediator mediator;

      /**
       * Constructor.
       * @param mediator The {@link KeYMediator} to use.
       * @param originalProof The {@link Proof} to generate test cases for.
       * @param showInMainWindow Defines if created {@link Proof}s are visible in the {@link MainWindow} or not.
       */
      public MainWindowTestGenerator(KeYMediator mediator, Proof originalProof, boolean showInMainWindow) {
         super(mediator.getUI(), originalProof);
         this.mediator = mediator;
         this.showInMainWindow = showInMainWindow;
      }
      
      /**
       * {@inheritDoc}
       */
      @Override
      public void dispose() {
         if (showInMainWindow) {
            List<Proof> proofs = getProofs();
            if (proofs == null) {
               return;
            }
            for (final Proof p : proofs) {
               if (MainWindow.getInstance().getProofList().containsProof(p)) {
                  p.dispose();
               }
            }
            mediator.setProof(getOriginalProof());
         }
         else {
            super.dispose();
         }
      }

      /**
       * {@inheritDoc}
       */
      @Override
      protected Proof createProof(UserInterfaceControl ui, Proof oldProof, String newName, Sequent newSequent) throws ProofInputException {
         if (showInMainWindow) {
            InitConfig initConfig = oldProof.getInitConfig().deepCopy();
            final Proof proof = new Proof(newName, newSequent, "", initConfig.createTacletIndex(), 
                  initConfig.createBuiltInRuleIndex(),
                  initConfig.deepCopy() );
            proof.setEnv(oldProof.getEnv());
            proof.setNamespaces(oldProof.getNamespaces());

            Services services = mediator.getServices();
            SpecificationRepository spec = services.getSpecificationRepository();
            spec.registerProof(spec.getProofOblInput(oldProof), proof);
            final ProofAggregate pa = new SingleProof(proof, "XXX");
            ui.registerProofAggregate(pa);
            return proof;
         }
         else {
            return super.createProof(ui, oldProof, newName, newSequent);
         }
      }

      /**
       * {@inheritDoc}
       */
      @Override
      protected void handleAllProofsPerformed(UserInterfaceControl ui) {
         mediator.setInteractive(true);
         mediator.startInterface(true);
      }
      
      /**
       * {@inheritDoc}
       */
      @Override
      protected void selectProof(UserInterfaceControl ui, Proof proof) {
         if (showInMainWindow) {
            mediator.setProof(proof);
         }
      }
   }

	@Override
	public Void doInBackground() {
		getMediator().setInteractive(false);
		getMediator().startInterface(false);
		SequentViewInputListener.setRefresh(false);
		testGenerator.generateTestCases(this, tgInfoDialog);
		return null;
	}

	/*
	 * finalise the GUI stuff
	 */
	@Override
	public void done() {
//	   testGenerator.removeGeneratedProofs(getMediator());
		getMediator().setInteractive(true);
		getMediator().startInterface(true);
		getMediator().removeInterruptedListener(this);
		SequentViewInputListener.setRefresh(true);
		originalProof = null;
	}

	@Override
	public void interruptionPerformed() {
		cancel(true);
		tgInfoDialog.writeln("\nStopping test case generation.");
		stop = true;
		testGenerator.stopSMTLauncher();
	}

	private KeYMediator getMediator(){
		return MainWindow.getInstance().getMediator();
	}

	public Proof getOriginalProof(){
		return originalProof;
	}

   @Override
   public boolean shouldStop() {
      return stop;
   }
}
