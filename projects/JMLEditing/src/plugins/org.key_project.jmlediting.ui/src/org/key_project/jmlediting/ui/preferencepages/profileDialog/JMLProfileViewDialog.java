package org.key_project.jmlediting.ui.preferencepages.profileDialog;

import org.eclipse.swt.SWT;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Shell;
import org.key_project.jmlediting.core.profile.IJMLProfile;

public class JMLProfileViewDialog extends AbstractJMLProfileDialog {

   private final Color redColor = Display.getCurrent().getSystemColor(
         SWT.COLOR_RED);

   public JMLProfileViewDialog(final Shell parent, final IJMLProfile profile) {
      super(parent, profile, "JML Profile Viewer", "");
   }

   @Override
   protected Control getDialogArea(final Composite composite) {
      final GridData data = new GridData(SWT.FILL, SWT.FILL, true, true);
      final Composite myComposite = new Composite(composite, SWT.NONE);
      myComposite.setLayoutData(data);
      myComposite.setLayout(this.getLayout());

      super.addProfileName(myComposite, false);

      this.addKeywordTableLabel(myComposite, "Supported Keywords");

      this.addKeywordTable(myComposite, 400);

      return composite;
   }

   @Override
   public void setProfile(final IJMLProfile profile) {
      super.setProfile(profile);
      this.profileNameText.setText(profile.getName());
   }
}
