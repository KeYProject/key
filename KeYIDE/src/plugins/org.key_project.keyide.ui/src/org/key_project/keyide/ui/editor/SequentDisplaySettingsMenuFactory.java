package org.key_project.keyide.ui.editor;

import org.eclipse.jface.action.Action;
import org.eclipse.jface.action.IMenuListener;
import org.eclipse.jface.action.IMenuManager;
import org.eclipse.jface.action.MenuManager;
import org.eclipse.ui.menus.ExtensionContributionFactory;
import org.eclipse.ui.menus.IContributionRoot;
import org.eclipse.ui.services.IServiceLocator;
import org.key_project.key4eclipse.common.ui.util.KeYImages;

import de.uka.ilkd.key.gui.actions.HidePackagePrefixToggleAction;
import de.uka.ilkd.key.gui.actions.PrettyPrintToggleAction;
import de.uka.ilkd.key.gui.actions.UnicodeToggleAction;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.settings.ProofIndependentSettings;

/**
 * Creates the "Sequent Display Settings" context menu which allows
 * to change the display settings of a Sequent.
 * @author Martin Hentschel
 */
public class SequentDisplaySettingsMenuFactory extends ExtensionContributionFactory {
   /**
    * The name of the "Sequent Display Settings" menu.
    */
   public static final String MENU_NAME = "Sequent Display Settings";
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void createContributionItems(IServiceLocator serviceLocator, IContributionRoot additions) {
      additions.addContributionItem(createSequentDisplaySettingsMenu(), null);
   }
   
   /**
    * Creates the {@link MenuManager} representing the "Sequent Display Settings" menu.
    * @return The created {@link MenuManager}.
    */
   public static MenuManager createSequentDisplaySettingsMenu() {
      MenuManager manager = new MenuManager();
      manager.setMenuText(MENU_NAME);
      manager.setImageDescriptor(KeYImages.getImageDescriptor(KeYImages.KEY_LOGO));
      manager.setRemoveAllWhenShown(true);
      manager.addMenuListener(new IMenuListener() {
         @Override
         public void menuAboutToShow(IMenuManager manager) {
            fillSequentDisplaySettingsMenu(manager);
         }
      });
      return manager;
   }
   
   /**
    * Fills the {@link IMenuManager} with the items of the "Sequent Display Settings" menu.
    * @param manager The {@link IMenuManager} to fill.
    */
   protected static void fillSequentDisplaySettingsMenu(IMenuManager manager) {
      // Pretty Syntax
      final boolean originalPrettyActionCheckedState = ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().isUsePretty();
      Action prettyAction = new Action(PrettyPrintToggleAction.NAME) {
         @Override
         public void run() {
            NotationInfo.DEFAULT_PRETTY_SYNTAX = !originalPrettyActionCheckedState; // Needs to be executed before the ViewSettings are modified, because the UI will react on the settings change event!
            ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().setUsePretty(!originalPrettyActionCheckedState);
         }
      };
      prettyAction.setToolTipText(PrettyPrintToggleAction.TOOL_TIP);
      prettyAction.setChecked(originalPrettyActionCheckedState);
      manager.add(prettyAction);
      // Use Unicode
      final boolean originalUnicodeActionCheckedState = ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().isUseUnicode();
      Action unicodeAction = new Action(UnicodeToggleAction.NAME) {
         @Override
         public void run() {
            NotationInfo.DEFAULT_UNICODE_ENABLED = !originalUnicodeActionCheckedState; // Needs to be executed before the ViewSettings are modified, because the UI will react on the settings change event!
            ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().setUseUnicode(!originalUnicodeActionCheckedState);
         }
      };
      unicodeAction.setToolTipText(UnicodeToggleAction.TOOL_TIP);
      unicodeAction.setChecked(originalUnicodeActionCheckedState);
      unicodeAction.setEnabled(originalPrettyActionCheckedState);
      manager.add(unicodeAction);
      // Hide Package Prefix
      final boolean originalPackageActionCheckedState = ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().isHidePackagePrefix();
      Action packageAction = new Action(HidePackagePrefixToggleAction.NAME) {
         @Override
         public void run() {
            NotationInfo.DEFAULT_HIDE_PACKAGE_PREFIX = !originalPackageActionCheckedState; // Needs to be executed before the ViewSettings are modified, because the UI will react on the settings change event!
            ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().setHidePackagePrefix(!originalPackageActionCheckedState);
         }
      };
      packageAction.setToolTipText(HidePackagePrefixToggleAction.TOOL_TIP);
      packageAction.setChecked(originalPackageActionCheckedState);
      packageAction.setEnabled(originalPrettyActionCheckedState);
      manager.add(packageAction);
   }
}
