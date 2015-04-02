package org.key_project.key4eclipse.common.ui.breakpoints;

import java.awt.event.ActionEvent;

import javax.swing.ImageIcon;
import javax.swing.JToggleButton;

import org.eclipse.debug.core.DebugPlugin;
import org.key_project.key4eclipse.common.ui.util.KeYImages;

import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.MainWindowAction;
import de.uka.ilkd.key.proof.Proof;

/**
 * This class adds support for breakpoints to the {@link MainWindow}.
 * @author Martin Hentschel
 */
public final class MainFrameBreakpointManager {
   /**
    * The extended {@link MainWindow}.
    */
   private static final MainWindow mainWindow = MainWindow.getInstance(false);

   /**
    * The used {@link BreakpointEnabledMainWindowAction}.
    */
   private static final BreakpointEnabledMainWindowAction action = new BreakpointEnabledMainWindowAction(mainWindow);
   
   /**
    * Listens for selection changes.
    */
   private static final KeYSelectionListener selectionListener = new KeYSelectionListener() {
      @Override
      public void selectedNodeChanged(KeYSelectionEvent e) {
      }

      @Override
      public void selectedProofChanged(KeYSelectionEvent e) {
         updateBreakpointManager();
      }
   };
   
   /**
    * The currently active {@link KeYBreakpointManager}.
    */
   private static KeYBreakpointManager breakpointManager;

   /**
    * Forbid instances.
    */
   private MainFrameBreakpointManager() {
   }

   /**
    * Starts the {@link MainWindow} extension.
    */
   public static void start() {
      // Add action to the MainWindow
      JToggleButton button = new JToggleButton(action);
      button.setHideActionText(true);
      mainWindow.getControlToolBar().add(button, 1);
      // Add selection listener
      mainWindow.getMediator().addKeYSelectionListener(selectionListener);
      // Create initial KeYBreakpointManager
      updateBreakpointManager();
   }

   /**
    * Stops the {@link MainWindow} extension.
    */
   public static void stop() {
      mainWindow.getMediator().removeKeYSelectionListener(selectionListener);
      if (breakpointManager != null) {
         DebugPlugin.getDefault().getBreakpointManager().removeBreakpointListener(breakpointManager);
      }
   }
   
   /**
    * Updates the used {@link KeYBreakpointManager} if the selected {@link Proof} has changed.
    */
   protected static void updateBreakpointManager() {
      Proof oldProof = breakpointManager != null ? breakpointManager.getProof() : null;
      Proof newProof = mainWindow.getMediator().getSelectedProof();
      if (oldProof != newProof) {
         if (breakpointManager != null) {
            DebugPlugin.getDefault().getBreakpointManager().removeBreakpointListener(breakpointManager);
         }
         if (newProof != null && !newProof.isDisposed()) {
            breakpointManager = new KeYBreakpointManager(newProof);
            DebugPlugin.getDefault().getBreakpointManager().addBreakpointListener(breakpointManager);
            breakpointManager.setEnabled(action.isSelected());
         }
         else {
            breakpointManager = null;
         }
      }
   }
   
   /**
    * The action show to the user to enable or disable suspension on breakpoints.
    * @author Martin Hentschel
    */
   private static final class BreakpointEnabledMainWindowAction extends MainWindowAction {
      /**
       * Generated UID.
       */
      private static final long serialVersionUID = 8591730144025506643L;

      /**
       * Constructor.
       * @param mainWindow The parent {@link MainWindow}.
       */
      protected BreakpointEnabledMainWindowAction(MainWindow mainWindow) {
         super(mainWindow);
         setName("Stop at Breakpoints");
         setTooltip("Stop when a breakpoint is hit.");
         setIcon(new ImageIcon(KeYImages.getURL(KeYImages.STOP_AT_BREAKPOINTS)));
         setSelected(Boolean.FALSE);
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public boolean isSelected() {
         return super.isSelected();
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public void actionPerformed(ActionEvent e) {
         if (breakpointManager != null) {
            breakpointManager.setEnabled(isSelected());
         }
      }
   }
}
