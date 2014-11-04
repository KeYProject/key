package org.key_project.jmlediting.ui;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.core.runtime.QualifiedName;
import org.eclipse.core.runtime.preferences.IEclipsePreferences;
import org.eclipse.core.runtime.preferences.InstanceScope;
import org.eclipse.jdt.internal.ui.preferences.PropertyAndPreferencePage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.List;

public class JMLProfilePropertiesPage extends PropertyAndPreferencePage {

   private List profilesList;

   public static final String JML_PROFILE_PREF_ID = "org.key_project.jmlediting.ui.preferences.profile";
   public static final String JML_PROFILE_PROP_ID = "org.key_project.jmlediting.ui.propertypages.profile";

   public static final QualifiedName PROFILE = new QualifiedName(
         "org.key_project.jmleiditing.ui", "profile");
   public static final String DEFAULT_JML_PROFILE = "default_jml_profile";

   public JMLProfilePropertiesPage() {
      // TODO Auto-generated constructor stub

   }

   @Override
   protected Control createPreferenceContent(Composite parent) {
      final Composite myComposite = new Composite(parent, SWT.NONE);
      final GridLayout layout = new GridLayout();
      layout.numColumns = 1;
      myComposite.setLayout(layout);

      GridData data;

      data = new GridData();
      data.grabExcessHorizontalSpace = true;
      data.grabExcessVerticalSpace = true;

      this.profilesList = new List(myComposite, SWT.V_SCROLL | SWT.SINGLE
            | SWT.BORDER);
      this.profilesList.setData(data);

      this.initUI();
      
      return myComposite;
   }

   @Override
   protected boolean hasProjectSpecificOptions(IProject project) {
      try {
         return project.getPersistentProperty(PROFILE) != null;
      }
      catch (CoreException e) {
         return false;
      }
   }

   @Override
   protected String getPreferencePageID() {
      return JML_PROFILE_PREF_ID;
   }

   @Override
   protected String getPropertyPageID() {
      return JML_PROFILE_PROP_ID;
   }
   
   
   private void initUI() {
      if (this.isProjectPreferencePage()) {
         // Project preferences
         
      } else {
         // Gobal preferences
      // global properties
         IEclipsePreferences preferences = InstanceScope.INSTANCE.getNode(Activator.PLUGIN_ID);
         String defaultProfile = preferences.get(DEFAULT_JML_PROFILE, null);
         
      }
   }
   

   @Override
   public boolean performOk() {
      if (this.isProjectPreferencePage()) {
         // Project preferences
         IProject project = this.getProject();
         try {
            if (this.useProjectSettings()) {
               // Set property
               // TODO
            }
            else {
               // Remove property
               project.setPersistentProperty(PROFILE, null);
            }
         }
         catch (CoreException e) {
            e.printStackTrace();
            // TODO
         }

      }
      else {
         // global properties
         IEclipsePreferences preferences = InstanceScope.INSTANCE.getNode(Activator.PLUGIN_ID);
         preferences.put(DEFAULT_JML_PROFILE, "TODO");
      }

      return super.performOk();
   }

}
