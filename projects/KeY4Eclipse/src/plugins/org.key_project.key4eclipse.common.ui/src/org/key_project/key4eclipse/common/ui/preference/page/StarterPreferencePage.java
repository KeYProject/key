package org.key_project.key4eclipse.common.ui.preference.page;

import org.eclipse.jface.preference.BooleanFieldEditor;
import org.eclipse.jface.preference.ComboFieldEditor;
import org.eclipse.jface.preference.FieldEditorPreferencePage;
import org.eclipse.jface.preference.PreferenceDialog;
import org.eclipse.jface.preference.PreferencePage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.layout.FillLayout;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Combo;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Group;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.swt.widgets.TabFolder;
import org.eclipse.swt.widgets.TabItem;
import org.eclipse.swt.widgets.Text;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;
import org.eclipse.ui.dialogs.PreferencesUtil;
import org.key_project.key4eclipse.common.ui.starter.IGlobalStarter;
import org.key_project.key4eclipse.common.ui.starter.IMethodStarter;
import org.key_project.key4eclipse.common.ui.util.LogUtil;
import org.key_project.key4eclipse.common.ui.util.StarterDescription;
import org.key_project.key4eclipse.common.ui.util.StarterPreferenceUtil;
import org.key_project.key4eclipse.common.ui.util.StarterUtil;
import org.key_project.util.eclipse.swt.SWTUtil;
import org.key_project.util.java.ObjectUtil;
import org.key_project.util.java.StringUtil;

import de.uka.ilkd.key.collection.ImmutableList;

/**
 * {@link PreferencePage} to define the used application starter.
 */
public class StarterPreferencePage extends FieldEditorPreferencePage implements IWorkbenchPreferencePage {
   /**
    * The ID of this preference page.
    */
   public static final String ID = "org.key_project.key4eclipse.common.ui.preference.page.StarterPreferencePage";
   
   /**
    * Constructor
    */
   public StarterPreferencePage() {
      super(GRID);
      setPreferenceStore(StarterPreferenceUtil.getStore());
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void init(IWorkbench workbench) {
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected void createFieldEditors() {
      TabFolder starterKindsTabFolder = new TabFolder(getFieldEditorParent(), SWT.NONE);
      starterKindsTabFolder.setLayoutData(new GridData(GridData.FILL_BOTH));
      // Global starter
      ImmutableList<StarterDescription<IGlobalStarter>> globalStarter = StarterUtil.getGlobalStarters();
      if (!globalStarter.isEmpty()) {
         createTab(starterKindsTabFolder, 
                   "Application", 
                   globalStarter, 
                   StarterPreferenceUtil.SELECTED_GLOBAL_STARTER_ID, 
                   StarterPreferenceUtil.DONT_ASK_FOR_GLOBAL_STARTER, 
                   StarterPreferenceUtil.GLOBAL_STARTER_DISABLED);
      }
      // Method starter
      ImmutableList<StarterDescription<IMethodStarter>> methodStarter = StarterUtil.getMethodStarters();
      if (!methodStarter.isEmpty()) {
         createTab(starterKindsTabFolder, 
                   "Proof of selected method", 
                   methodStarter, 
                   StarterPreferenceUtil.SELECTED_METHOD_STARTER_ID, 
                   StarterPreferenceUtil.DONT_ASK_FOR_METHOD_STARTER, 
                   StarterPreferenceUtil.METHOD_STARTER_DISABLED);
      }
   }
   
   /**
    * Creates a tab.
    * @param starterKindsTabFolder The {@link TabFolder} to fill.
    * @param tabTitle The tab title.
    * @param starterDescriptions The available {@link StarterDescription}s.
    * @param selectedStarterProperty The property to store the selected {@link StarterDescription}.
    * @param dontAskAgainProperty The property to store the do not ask again value.
    * @param disableProperty The property to store the disabled value.
    */
   protected <I> void createTab(TabFolder starterKindsTabFolder,
                                String tabTitle,
                                final ImmutableList<StarterDescription<I>> starterDescriptions,
                                String selectedStarterProperty,
                                String dontAskAgainProperty,
                                String disableProperty) {
      final Composite globalStarterTabComposite = new Composite(starterKindsTabFolder, SWT.NONE);
      globalStarterTabComposite.setLayout(new GridLayout(1, false));
      
      final String[][] globalStarterEntries = new String[starterDescriptions.size()][];
      int i = 0;
      for (StarterDescription<I> sd : starterDescriptions) {
         globalStarterEntries[i] = new String[] {sd.getName(), sd.getId()};
         i++;
      }
      final ComboFieldEditor selectedGlobalStarterEditor = new ComboFieldEditor(selectedStarterProperty, "Selected Application", globalStarterEntries, globalStarterTabComposite);
      addField(selectedGlobalStarterEditor);
      
      Group descriptionGroup = new Group(globalStarterTabComposite, SWT.NONE);
      GridData descriptionGroupData = new GridData(GridData.FILL_BOTH);
      descriptionGroupData.widthHint = 400;
      descriptionGroup.setLayoutData(descriptionGroupData);
      descriptionGroup.setText("Description");
      descriptionGroup.setLayout(new FillLayout());
      final Text descriptionText = new Text(descriptionGroup, SWT.BORDER | SWT.V_SCROLL | SWT.MULTI | SWT.WRAP);
      descriptionText.setEditable(false);
      StarterDescription<I> initialSd = StarterUtil.searchGlobalStarter(starterDescriptions, getPreferenceStore().getString(selectedStarterProperty));
      if (initialSd == null && !starterDescriptions.isEmpty()) {
         initialSd = starterDescriptions.head();
      }
      if (initialSd != null) {
         SWTUtil.setText(descriptionText, initialSd.getDescription());
      }
      try {
         final Combo combo = (Combo)ObjectUtil.get(selectedGlobalStarterEditor, "fCombo");
         combo.addSelectionListener(new SelectionAdapter() {
            @Override
            public void widgetSelected(SelectionEvent e) {
              int index = combo.getSelectionIndex();
              if (index >= 0 && index < starterDescriptions.size()) {
                 SWTUtil.setText(descriptionText, starterDescriptions.take(index).head().getDescription());
              }
              else {
                 descriptionText.setText(StringUtil.EMPTY_STRING);
              }
            }
         });
      }
      catch (Exception e) {
         LogUtil.getLogger().logError(e);
      }
      
      final BooleanFieldEditor dontAskEditor = new BooleanFieldEditor(dontAskAgainProperty, "&Do not ask", globalStarterTabComposite);
      addField(dontAskEditor);

      BooleanFieldEditor disabledEditor = new BooleanFieldEditor(disableProperty, "D&isable functionality", globalStarterTabComposite);
      addField(disabledEditor);
      try {
         final Button button = (Button)ObjectUtil.get(disabledEditor, "checkBox");
         button.addSelectionListener(new SelectionAdapter() {
            @Override
            public void widgetSelected(SelectionEvent e) {
               boolean disabled = button.getSelection();
               selectedGlobalStarterEditor.setEnabled(!disabled, globalStarterTabComposite);
               descriptionText.setEnabled(!disabled);
               dontAskEditor.setEnabled(!disabled, globalStarterTabComposite);
            }
         });
      }
      catch (Exception e) {
         LogUtil.getLogger().logError(e);
      }

      TabItem globalStarterTabItem = new TabItem(starterKindsTabFolder, SWT.NONE);
      globalStarterTabItem.setText(tabTitle);
      globalStarterTabItem.setControl(globalStarterTabComposite);
      
      boolean disabled = getPreferenceStore().getBoolean(disableProperty);
      selectedGlobalStarterEditor.setEnabled(!disabled, globalStarterTabComposite);
      descriptionText.setEnabled(!disabled);
      dontAskEditor.setEnabled(!disabled, globalStarterTabComposite);
   }

   /**
    * Opens the {@link PreferencePage} and shows this {@link PreferencePage}.
    * @param parentShell The parent {@link Shell}.
    * @return The dialog result.
    */
   public static int openPreferencePage(Shell parentShell) {
      PreferenceDialog dialog = PreferencesUtil.createPreferenceDialogOn(parentShell, ID, null, null);
      if (dialog != null) {
         return dialog.open();
      }
      else {
         return PreferenceDialog.CANCEL;
      }
   }
}
