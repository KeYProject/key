package org.key_project.stubby.ui.customization;

import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.key_project.stubby.core.customization.IGeneratorCustomization;
import org.key_project.stubby.ui.wizard.page.GenerateStubsWizardPage;

/**
 * Instances of this interface are used to customize the stub generation process.
 * @author Martin Hentschel
 */
public interface IStubGenerationCustomization {
   /**
    * Initializes this {@link IStubGenerationCustomization}.
    * @param javaProject The {@link IJavaProject} to generate stubs for.
    */
   public void init(IJavaProject javaProject);
   
   /**
    * Creates a {@link Control} which will be shown in the {@link GenerateStubsWizardPage}.
    * @param parent The parent {@link Composite}.
    * @return The created {@link Control} or {@code null} if nothing should be shown.
    */
   public Control createComposite(Composite parent);

   /**
    * Sets the defined stub folder path.
    * @param stubFolderPath The stub folder path.
    */
   public void setStubFolderPath(String stubFolderPath);
   
   /**
    * Creates the {@link IGeneratorCustomization} to consider during stub generation.
    * @return The {@link IGeneratorCustomization} to consider during stub generation.
    */
   public IGeneratorCustomization createGeneratorCustomization();
}
