package org.key_project.jmlediting.ui.preferencepages.profileDialog;

import org.eclipse.jface.dialogs.IMessageProvider;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Shell;
import org.key_project.jmlediting.core.profile.IEditableDerivedProfile;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.InvalidProfileException;
import org.key_project.jmlediting.core.profile.JMLProfileManagement;

public class JMLProfileNewDialog extends AbstractJMLProfileDialog {

   public JMLProfileNewDialog(final Shell parent) {
      super(parent, null, "New JML Profile", "");
   }

   @Override
   protected Control getDialogArea(final Composite composite) {
      final Composite myComposite = new Composite(composite, SWT.NONE);
      myComposite.setLayout(this.getLayout());
      myComposite.setLayoutData(new GridData(SWT.LEFT, SWT.TOP, false, false));

      this.addProfileName(myComposite, true);

      this.addDerivedFrom(myComposite, true);

      this.addKeywordTableLabel(myComposite, "Supported Keywords");

      this.addKeywordTable(myComposite, 400);

      this.derivedFromCombo.addSelectionListener(new SelectionListener() {

         @Override
         public void widgetSelected(final SelectionEvent e) {
            final IJMLProfile profile = JMLProfileNewDialog.this
                  .getSelectedProfileFromCombo();
            JMLProfileNewDialog.this.setProfile(profile);
         }

         @Override
         public void widgetDefaultSelected(final SelectionEvent e) {
         }
      });

      return composite;
   }

   @Override
   protected void okPressed() {
      final String profileName = this.profileNameText.getText();
      final String profileId = this.generateId(profileName);
      final IJMLProfile parentProfile = this.getSelectedProfileFromCombo();

      if (profileName.isEmpty() || parentProfile == null) {
         this.setMessage(PLEASE_RESOLVE, IMessageProvider.ERROR);
         return;
      }
      else {
         this.setMessage("", IMessageProvider.NONE);
      }

      if (!this.checkProfileNameUnique(profileId)) {
         return;
      }

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
      final int index = this.derivedFromCombo.getSelectionIndex();
      if (index == -1) {
         return null;
      }
      return (IJMLProfile) this.derivedFromCombo.getData(this.derivedFromCombo
            .getItem(index));
   }
}
