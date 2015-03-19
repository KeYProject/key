package org.key_project.jmlediting.ui.preferencepages.profileDialog;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.Iterator;
import java.util.List;

import org.eclipse.jface.dialogs.IMessageProvider;
import org.eclipse.jface.dialogs.TitleAreaDialog;
import org.eclipse.jface.fieldassist.ControlDecoration;
import org.eclipse.jface.fieldassist.FieldDecorationRegistry;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.ModifyEvent;
import org.eclipse.swt.events.ModifyListener;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Combo;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Layout;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.swt.widgets.Table;
import org.eclipse.swt.widgets.TableColumn;
import org.eclipse.swt.widgets.TableItem;
import org.eclipse.swt.widgets.Text;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.JMLProfileManagement;
import org.key_project.jmlediting.core.profile.syntax.IKeyword;
import org.key_project.jmlediting.ui.util.JMLSWTUtil;

public abstract class AbstractJMLProfileDialog extends TitleAreaDialog {
   protected static final String PLEASE_RESOLVE = "Please resolve the errors before saving!";

   private IJMLProfile profile;

   private Table keywordTable;

   private final String title;
   private final String message;

   protected Text profileNameText;
   protected ControlDecoration profileNameError;
   protected Combo derivedFromCombo;
   protected ControlDecoration comboError;

   public AbstractJMLProfileDialog(final Shell parent,
         final IJMLProfile profile, final String title, final String message) {
      super(parent);
      this.title = title;
      this.message = message;
      this.profile = profile;
      this.setShellStyle(super.getShellStyle() | SWT.RESIZE | SWT.FILL);
      this.setHelpAvailable(false);
   }

   @Override
   public void create() {
      super.create();
      this.setTitle(this.title);
      if (!this.message.isEmpty()) {
         this.setMessage(this.message, IMessageProvider.INFORMATION);
      }
      else {
         this.setMessage(this.message);
      }
   }

   @Override
   protected Control createDialogArea(final Composite parent) {
      final Control result = this.getDialogArea((Composite) super
            .createDialogArea(parent));

      if (this.profile != null) {
         this.setProfile(this.profile);
      }

      return result;
   }

   protected abstract Control getDialogArea(final Composite composite);

   public void setProfile(final IJMLProfile profile) {
      this.profile = profile;

      this.fillKeywordTable();
   }

   protected Button createTableSideButton(final Composite myComposite,
         final String name) {
      final Button button = new Button(myComposite, SWT.PUSH);
      button.setText(name);
      button.setLayoutData(new GridData(SWT.FILL, SWT.TOP, false, false, 1, 1));

      return button;
   }

   protected String[] keywordToTableData(final IKeyword keyword) {
      String sourceDescription = keyword.getDescription();
      if (sourceDescription != null && sourceDescription.length() > 200) {
         sourceDescription = sourceDescription.substring(0, 196);
         sourceDescription += " ...";
         sourceDescription = sourceDescription.replace('\n', ' ');
      }
      final Iterator<String> iterator = keyword.getKeywords().iterator();
      String keywordString = iterator.next();
      while (iterator.hasNext()) {
         keywordString = keywordString + ", " + iterator.next();
      }

      return new String[] { keywordString, sourceDescription };
   }

   protected IJMLProfile getProfileToEdit() {
      return this.profile;
   }

   protected Table getKeywordTable() {
      return this.keywordTable;
   }

   protected void setKeywordTable(final Table keywordTable) {
      this.keywordTable = keywordTable;
   }

   protected void addDerivedFrom(final Composite myComposite,
         final boolean enabled) {
      GridData data;
      data = new GridData(SWT.FILL, SWT.TOP, false, true);
      data.horizontalSpan = 1;
      final Label derivedFromLabel = new Label(myComposite, SWT.NONE);
      derivedFromLabel.setText("Derived from: ");
      derivedFromLabel.setLayoutData(data);

      data = new GridData(SWT.LEFT, SWT.TOP, true, true);
      data.horizontalSpan = 2;
      data.widthHint = 200;
      this.derivedFromCombo = new Combo(myComposite, SWT.BORDER | SWT.READ_ONLY);
      this.derivedFromCombo.setLayoutData(data);
      JMLSWTUtil.fillComboWithParentProfilesAndDate(this.derivedFromCombo);
      this.derivedFromCombo.setEnabled(enabled);

      this.comboError = new ControlDecoration(this.derivedFromCombo, SWT.RIGHT
            | SWT.TOP);
      this.comboError.setImage(FieldDecorationRegistry.getDefault()
            .getFieldDecoration(FieldDecorationRegistry.DEC_ERROR).getImage());
      this.comboError
            .setDescriptionText("Please select a profile to derive from!");
      this.comboError.show();

      this.derivedFromCombo.addModifyListener(new ModifyListener() {
         @Override
         public void modifyText(final ModifyEvent e) {
            final int index = AbstractJMLProfileDialog.this.derivedFromCombo
                  .getSelectionIndex();
            if (index == -1) {
               AbstractJMLProfileDialog.this.comboError.show();
            }
            else {
               AbstractJMLProfileDialog.this.comboError.hide();
            }
         }
      });
   }

   protected void addProfileName(final Composite myComposite,
         final boolean enabled) {
      GridData data;
      data = new GridData(SWT.FILL, SWT.TOP, false, true);
      data.horizontalSpan = 1;
      final Label profileNameLabel = new Label(myComposite, SWT.NONE);
      profileNameLabel.setText("ProfileName: ");
      profileNameLabel.setLayoutData(data);

      data = new GridData(SWT.LEFT, SWT.TOP, true, true);
      data.horizontalSpan = 2;
      data.widthHint = 200;
      this.profileNameText = new Text(myComposite, SWT.SINGLE | SWT.BORDER);
      this.profileNameText.setLayoutData(data);
      this.profileNameText.setEnabled(enabled);

      this.profileNameError = new ControlDecoration(this.profileNameText,
            SWT.RIGHT | SWT.TOP);
      this.profileNameError.setImage(FieldDecorationRegistry.getDefault()
            .getFieldDecoration(FieldDecorationRegistry.DEC_ERROR).getImage());
      this.profileNameError
            .setDescriptionText("Profile name must not be empty!");
      this.profileNameError.show();

      this.profileNameText.addModifyListener(new ModifyListener() {
         @Override
         public void modifyText(final ModifyEvent e) {
            if (AbstractJMLProfileDialog.this.profileNameText.getText()
                  .isEmpty()) {
               AbstractJMLProfileDialog.this.profileNameError
                     .setDescriptionText("Profile name must not be empty!");
               AbstractJMLProfileDialog.this.profileNameError.show();
            }
            else {
               AbstractJMLProfileDialog.this.profileNameError.hide();
            }
         }
      });
   }

   protected void addKeywordTableLabel(final Composite myComposite,
         final String text) {
      GridData data;
      data = new GridData(SWT.LEFT, SWT.TOP, false, false, 1, 1);
      data.horizontalSpan = 3;
      data.verticalIndent = 20;
      final Label keywordTableLabel = new Label(myComposite, SWT.NONE);
      keywordTableLabel.setText(text);
      keywordTableLabel.setLayoutData(data);
   }

   protected void addDerivedTableLabel(final Composite myComposite) {
      GridData data;
      data = new GridData(SWT.LEFT, SWT.TOP, false, false, 1, 1);
      data.horizontalSpan = 3;
      data.verticalIndent = 20;
      final Label derivedTableLabel = new Label(myComposite, SWT.NONE);
      derivedTableLabel.setText("Custom Keywords: ");
      derivedTableLabel.setLayoutData(data);
   }

   protected void addKeywordTable(final Composite myComposite, final int height) {
      GridData data;
      data = new GridData(SWT.FILL, SWT.TOP, true, true);
      data.heightHint = height;
      data.horizontalSpan = 2;
      this.keywordTable = new Table(myComposite, SWT.H_SCROLL | SWT.V_SCROLL
            | SWT.BORDER | SWT.FULL_SELECTION);
      this.keywordTable.setLayoutData(data);
      this.keywordTable.setHeaderVisible(true);
      this.keywordTable.setLinesVisible(true);

      final TableColumn genericKeywordTableColumn = new TableColumn(
            this.keywordTable, SWT.LEFT);
      genericKeywordTableColumn.setText("Keyword");
      genericKeywordTableColumn.setWidth(150);

      final TableColumn genericDescriptionTableColumn = new TableColumn(
            this.keywordTable, SWT.LEFT);
      genericDescriptionTableColumn.setText("Description");
      genericDescriptionTableColumn.setWidth(300);
   }

   protected IKeyword getSelectedParentKeyword() {
      final TableItem selectedItem = this.getSelectedParentTableItem();
      return (IKeyword) selectedItem.getData();
   }

   protected TableItem getSelectedParentTableItem() {
      return this.keywordTable.getSelection()[0];
   }

   @Override
   protected Layout getLayout() {
      return new GridLayout(3, false);
   }

   protected void fillKeywordTable() {
      if (this.keywordTable == null) {
         return;
      }

      this.keywordTable.removeAll();
      final List<IKeyword> keywordList = new ArrayList<IKeyword>(
            this.profile.getSupportedKeywords());

      Collections.sort(keywordList, new Comparator<IKeyword>() {
         @Override
         public int compare(final IKeyword o1, final IKeyword o2) {
            return o1.getKeywords().iterator().next()
                  .compareTo(o2.getKeywords().iterator().next());
         }
      });
      for (final IKeyword keyword : keywordList) {
         final TableItem item = new TableItem(this.keywordTable, 0);
         item.setText(this.keywordToTableData(keyword));
      }

      this.keywordTable.setEnabled(true);
      this.keywordTable.redraw();
   }

   protected boolean checkProfileNameUnique(final String profileId) {
      if (JMLProfileManagement.instance().getProfileFromIdentifier(profileId) != null) {
         this.profileNameError
               .setDescriptionText("Profile Name already exists!");
         this.setMessage(PLEASE_RESOLVE, IMessageProvider.ERROR);
         this.profileNameError.show();
         return false;
      }
      else {
         this.setMessage("", IMessageProvider.NONE);
         this.profileNameError.hide();
         return true;
      }
   }

   protected String generateId(final String profileName) {
      return "user.defined.profile." + profileName.replaceAll("\\s", "");
   }

}