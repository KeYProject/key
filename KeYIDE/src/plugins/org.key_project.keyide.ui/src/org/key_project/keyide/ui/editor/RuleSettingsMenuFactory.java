package org.key_project.keyide.ui.editor;

import org.eclipse.jface.action.Action;
import org.eclipse.jface.action.IMenuListener;
import org.eclipse.jface.action.IMenuManager;
import org.eclipse.jface.action.MenuManager;
import org.eclipse.ui.menus.ExtensionContributionFactory;
import org.eclipse.ui.menus.IContributionRoot;
import org.eclipse.ui.services.IServiceLocator;
import org.key_project.key4eclipse.common.ui.util.KeYImages;
import org.key_project.key4eclipse.starter.core.util.IProofProvider;

import de.uka.ilkd.key.gui.actions.MinimizeInteraction;
import de.uka.ilkd.key.gui.actions.OneStepSimplificationToggleAction;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.settings.ProofIndependentSettings;

/**
 * Creates the "Rule Settings" context menu which allows
 * to change the rule settings.
 * @author Martin Hentschel
 */
public class RuleSettingsMenuFactory extends ExtensionContributionFactory {
   /**
    * The name of the "Rule Settings" menu.
    */
   public static final String MENU_NAME = "Rule Settings";
   
   /**
    * The ID of the "Rule Settings" menu.
    */
   public static final String MENU_ID = "ruleSettings";
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void createContributionItems(IServiceLocator serviceLocator, IContributionRoot additions) {
      IProofProvider proofProvider = (IProofProvider) serviceLocator.getService(IProofProvider.class);
      additions.addContributionItem(createSequentDisplaySettingsMenu(proofProvider), null);
   }
   
   /**
    * Creates the {@link MenuManager} representing the "Rule Settings" menu.
    * @param proofProvider The active {@link IProofProvider}.
    * @return The created {@link MenuManager}.
    */
   public static MenuManager createSequentDisplaySettingsMenu(final IProofProvider proofProvider) {
      MenuManager manager = new MenuManager(MENU_NAME, MENU_ID);
      manager.setImageDescriptor(KeYImages.getImageDescriptor(KeYImages.KEY_LOGO));
      manager.setRemoveAllWhenShown(true);
      manager.addMenuListener(new IMenuListener() {
         @Override
         public void menuAboutToShow(IMenuManager manager) {
            fillSequentDisplaySettingsMenu(manager, proofProvider);
         }
      });
      return manager;
   }
   
   /**
    * Fills the {@link IMenuManager} with the items of the "Rule Settings" menu.
    * @param manager The {@link IMenuManager} to fill.
    * @param proofProvider The active {@link IProofProvider}.
    */
   protected static void fillSequentDisplaySettingsMenu(IMenuManager manager, IProofProvider proofProvider) {
      // Get current proof and its profile
      Proof proof = proofProvider != null ? 
                    proofProvider.getCurrentProof() : 
                    null;
      Profile profile = proof != null && !proof.isDisposed() ? 
                        proof.getServices().getProfile() : 
                        null;
      // Taclet filter
      final boolean originalTacletFilterCheckedState = ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings().tacletFilter();
      Action tacletFilterAction = new Action(MinimizeInteraction.NAME) {
         @Override
         public void run() {
            ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings().setTacletFilter(!originalTacletFilterCheckedState);
         }
      };
      tacletFilterAction.setToolTipText(MinimizeInteraction.TOOL_TIP);
      tacletFilterAction.setChecked(originalTacletFilterCheckedState);
      manager.add(tacletFilterAction);
      // One step simplification
      final boolean originalOSSCheckedState = ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings().oneStepSimplification();
      Action oSSAction = new Action(OneStepSimplificationToggleAction.NAME) {
         @Override
         public void run() {
            ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings().setOneStepSimplification(!originalOSSCheckedState);
         }
      };
      oSSAction.setChecked(originalOSSCheckedState);
      oSSAction.setEnabled(profile instanceof JavaProfile);
      manager.add(oSSAction);
   }
}
