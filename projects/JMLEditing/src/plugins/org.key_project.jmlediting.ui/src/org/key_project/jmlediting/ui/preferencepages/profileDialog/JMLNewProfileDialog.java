package org.key_project.jmlediting.ui.preferencepages.profileDialog;

import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Shell;
import org.key_project.jmlediting.core.profile.IEditableDerivedProfile;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.InvalidProfileException;
import org.key_project.jmlediting.core.profile.JMLProfileManagement;

public class JMLNewProfileDialog extends AbstractJMLProfileDialog {

   public JMLNewProfileDialog(final Shell parent) {
      super(parent, null, "New JML Profile", "");
   }

   @Override
   protected Control getDialogArea(final Composite composite) {
      final Composite myComposite = new Composite(composite, SWT.NONE);
      myComposite.setLayout(new GridLayout(3, false));
      myComposite.setLayoutData(new GridData(SWT.LEFT, SWT.TOP, false, false));

      this.addProfileName(myComposite, true);

      this.addDerivedFrom(myComposite, true);

      this.addKeywordTableLabel(myComposite, "Supported Keywords");

      this.addKeywordTable(myComposite, 400);

      this.derivedFromCombo.addSelectionListener(new SelectionListener() {

         @Override
         public void widgetSelected(final SelectionEvent e) {
            final IJMLProfile profile = JMLNewProfileDialog.this
                  .getSelectedProfileFromCombo();
            JMLNewProfileDialog.this.setProfile(profile);
         }

         @Override
         public void widgetDefaultSelected(final SelectionEvent e) {
         }
      });

      // final GridData labelData = new GridData(SWT.FILL, SWT.CENTER, false,
      // true);
      // final GridData textData = new GridData(SWT.FILL, SWT.CENTER, false,
      // true);
      //
      // final Label profileNameLabel = new Label(myComposite, SWT.NONE);
      // profileNameLabel.setText("Profile Name: ");
      // profileNameLabel.setLayoutData(labelData);
      //
      // this.profileNameText = new Text(myComposite, SWT.SINGLE | SWT.BORDER);
      // this.profileNameText.setLayoutData(textData);
      //
      // final Label profileIdLabel = new Label(myComposite, SWT.NONE);
      // profileIdLabel.setText("Profile ID: ");
      // profileIdLabel.setLayoutData(labelData);
      //
      // this.profileIdText = new Text(myComposite, SWT.SINGLE | SWT.BORDER);
      // this.profileIdText.setLayoutData(textData);
      //
      // final Label derivedFromLabel = new Label(myComposite, SWT.NONE);
      // derivedFromLabel.setText("Derived from: ");
      // derivedFromLabel.setLayoutData(labelData);
      //
      // this.derivedFromCombo = new Combo(myComposite, SWT.READ_ONLY |
      // SWT.BORDER);
      // JMLSWTUtil.fillComboWithParentProfilesAndDate(this.derivedFromCombo);
      // this.derivedFromCombo.setLayoutData(textData);
      //
      // this.derivedFromCombo.addSelectionListener(new SelectionListener() {
      // @Override
      // public void widgetSelected(final SelectionEvent e) {
      // }
      //
      // @Override
      // public void widgetDefaultSelected(final SelectionEvent e) {
      // }
      // });
      //
      return composite;
   }

   @Override
   protected void okPressed() {
      final String profileName = this.profileNameText.getText();
      final String profileId = this.generateId(profileName);
      final IJMLProfile parentProfile = this.getSelectedProfileFromCombo();

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

   private IJMLProfile getSelectedProfileFromCombo() {
      return (IJMLProfile) this.derivedFromCombo.getData(this.derivedFromCombo
            .getItem(this.derivedFromCombo.getSelectionIndex()));
   }

   private String generateId(final String profileName) {
      return "user.defined.profile." + profileName.replaceAll("\\s", "");
   }
}
