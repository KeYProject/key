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
   }
}
