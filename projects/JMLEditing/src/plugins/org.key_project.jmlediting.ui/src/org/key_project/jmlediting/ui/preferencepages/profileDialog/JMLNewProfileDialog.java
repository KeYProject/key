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
import org.key_project.jmlediting.core.profile.DerivedProfile;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.InvalidProfileException;
import org.key_project.jmlediting.core.profile.JMLProfileHelper;
import org.key_project.jmlediting.core.profile.JMLProfileManagement;

public class JMLNewProfileDialog extends StatusDialog {

   private Text profileNameText;
   private Text profileIdText;
   private Combo derivedFromCombo;

   public JMLNewProfileDialog(final Shell parent) {
      super(parent);
      this.setTitle("New JML Profile");
   }

   @Override
   protected Control createDialogArea(final Composite parent) {
      final Composite composite = (Composite) super.createDialogArea(parent);

      GridData data = new GridData(SWT.FILL, SWT.FILL, true, true);
      final Composite myComposite = new Composite(composite, SWT.NONE);
      myComposite.setLayoutData(data);
      myComposite.setLayout(new GridLayout(2, false));

      data = new GridData(SWT.FILL, SWT.FILL, false, true);

      final Label profileNameLabel = new Label(myComposite, SWT.NONE);
      profileNameLabel.setText("Profile Name: ");
      profileNameLabel.setLayoutData(data);

      this.profileNameText = new Text(myComposite, SWT.SINGLE | SWT.BORDER);
      this.profileNameText.setLayoutData(data);

      final Label profileIdLabel = new Label(myComposite, SWT.NONE);
      profileIdLabel.setText("Profile ID: ");
      profileIdLabel.setLayoutData(data);

      this.profileIdText = new Text(myComposite, SWT.SINGLE | SWT.BORDER);
      this.profileIdText.setLayoutData(data);

      final Label derivedFromLabel = new Label(myComposite, SWT.NONE);
      derivedFromLabel.setText("Derived from: ");
      derivedFromLabel.setLayoutData(data);

      this.derivedFromCombo = new Combo(myComposite, SWT.READ_ONLY | SWT.BORDER);
      JMLProfileHelper
            .fillComboWithParentProfilesAndDate(this.derivedFromCombo);
      this.derivedFromCombo.setLayoutData(data);

      return composite;
   }

   @Override
   protected void okPressed() {
      final String profileName = this.profileNameText.getText();
      final String profileId = this.profileIdText.getText();
      final IJMLProfile parentProfile = (IJMLProfile) this.derivedFromCombo
            .getData(this.derivedFromCombo.getItem(this.derivedFromCombo
                  .getSelectionIndex()));

      final DerivedProfile newProfile = new DerivedProfile(profileName,
            profileId, parentProfile);

      try {
         JMLProfileManagement.instance().addDerivedProfile(newProfile);
         JMLProfileManagement.instance().writeDerivedProfiles();
      }
      catch (final InvalidProfileException ipe) {
         ipe.printStackTrace();
         return;
      }

      super.okPressed();
   }
}
