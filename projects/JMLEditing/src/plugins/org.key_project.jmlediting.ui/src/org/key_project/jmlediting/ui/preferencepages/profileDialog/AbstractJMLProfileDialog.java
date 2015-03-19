package org.key_project.jmlediting.ui.preferencepages.profileDialog;

import java.util.Iterator;

import org.eclipse.jface.dialogs.IMessageProvider;
import org.eclipse.jface.dialogs.TitleAreaDialog;
import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.swt.widgets.Table;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.syntax.IKeyword;

public abstract class AbstractJMLProfileDialog extends TitleAreaDialog {

   private IJMLProfile profile;

   private Table keywordTable;

   private final String title;
   private final String message;

   public AbstractJMLProfileDialog(final Shell parent,
         final IJMLProfile profile, final String title, final String message) {
      super(parent);
      this.title = title;
      this.message = message;
      this.profile = profile;
      this.setShellStyle(super.getShellStyle() | SWT.RESIZE | SWT.FILL);
   }

   @Override
   public void create() {
      super.create();
      this.setTitle(this.title);
      this.setMessage(this.message, IMessageProvider.INFORMATION);
   }

   abstract public void setProfile(final IJMLProfile profile);

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

   protected void setProfileToEdit(final IJMLProfile profileToEdit) {
      this.profile = profileToEdit;
   }

   protected Table getKeywordTable() {
      return this.keywordTable;
   }

   protected void setKeywordTable(final Table keywordTable) {
      this.keywordTable = keywordTable;
   }

}