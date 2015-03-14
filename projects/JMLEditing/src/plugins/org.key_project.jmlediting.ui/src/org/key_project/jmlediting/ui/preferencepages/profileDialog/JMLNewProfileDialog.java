package org.key_project.jmlediting.ui.preferencepages.profileDialog;

import org.eclipse.jface.dialogs.StatusDialog;
import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Combo;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.swt.widgets.Text;
import org.key_project.jmlediting.core.profile.IEditableDerivedProfile;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.InvalidProfileException;
import org.key_project.jmlediting.core.profile.JMLProfileManagement;
import org.key_project.jmlediting.ui.util.JMLSWTUtil;

public class JMLNewProfileDialog extends StatusDialog {

   private Text profileNameText;
   private Text profileIdText;
   private Combo derivedFromCombo;

   public JMLNewProfileDialog(final Shell parent) {
      super(parent);
      this.setTitle("New JML Profile");
      this.setShellStyle(super.getShellStyle() | SWT.RESIZE | SWT.FILL);
   }

   @Override
   protected Control createDialogArea(final Composite parent) {
      final Composite composite = (Composite) super.createDialogArea(parent);

      final Composite myComposite = new Composite(composite, SWT.NONE);
      myComposite.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));
      myComposite.setLayout(new GridLayout(2, false));

      final GridData labelData = new GridData(SWT.FILL, SWT.CENTER, false, true);
      final GridData textData = new GridData(SWT.FILL, SWT.CENTER, false, true);

      final Label profileNameLabel = new Label(myComposite, SWT.NONE);
      profileNameLabel.setText("Profile Name: ");
      profileNameLabel.setLayoutData(labelData);

      this.profileNameText = new Text(myComposite, SWT.SINGLE | SWT.BORDER);
      this.profileNameText.setLayoutData(textData);

      final Label profileIdLabel = new Label(myComposite, SWT.NONE);
      profileIdLabel.setText("Profile ID: ");
      profileIdLabel.setLayoutData(labelData);

      this.profileIdText = new Text(myComposite, SWT.SINGLE | SWT.BORDER);
      this.profileIdText.setLayoutData(textData);

      final Label derivedFromLabel = new Label(myComposite, SWT.NONE);
      derivedFromLabel.setText("Derived from: ");
      derivedFromLabel.setLayoutData(labelData);

      this.derivedFromCombo = new Combo(myComposite, SWT.READ_ONLY | SWT.BORDER);
      JMLSWTUtil.fillComboWithParentProfilesAndDate(this.derivedFromCombo);
      this.derivedFromCombo.setLayoutData(textData);

      // TODO validate

      return composite;
   }

   @Override
   protected void okPressed() {
      final String profileName = this.profileNameText.getText();
      final String profileId = this.profileIdText.getText();
      final IJMLProfile parentProfile = (IJMLProfile) this.derivedFromCombo
            .getData(this.derivedFromCombo.getItem(this.derivedFromCombo
                  .getSelectionIndex()));

      final IEditableDerivedProfile newProfile = parentProfile.derive(
            profileId, profileName);

      try {
         JMLProfileManagement.instance().addUserDefinedProfile(newProfile);
         JMLProfileManagement.instance().writeDerivedProfiles();
      }
      catch (final InvalidProfileException ipe) {
         ipe.printStackTrace();
         return;
      }

      super.okPressed();
   }
}
