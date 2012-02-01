package org.key_project.sed.key.ui.launch;

import java.util.Collections;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.debug.core.ILaunchConfigurationWorkingCopy;
import org.eclipse.debug.ui.AbstractLaunchConfigurationTab;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.jdt.core.IType;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.core.search.IJavaSearchScope;
import org.eclipse.jdt.core.search.SearchEngine;
import org.eclipse.jdt.debug.ui.launchConfigurations.JavaMainTab;
import org.eclipse.jdt.internal.debug.ui.launcher.AbstractJavaMainTab;
import org.eclipse.jdt.internal.debug.ui.launcher.DebugTypeSelectionDialog;
import org.eclipse.jdt.ui.JavaElementLabelProvider;
import org.eclipse.jface.viewers.ILabelProvider;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.ModifyEvent;
import org.eclipse.swt.events.ModifyListener;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Group;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Text;
import org.eclipse.ui.dialogs.ElementListSelectionDialog;
import org.key_project.key4eclipse.util.jdt.JDTUtil;
import org.key_project.sed.key.core.util.KeySEDUtil;
import org.key_project.sed.key.ui.jdt.AllMethodsSearchEngine;
import org.key_project.sed.key.ui.jdt.AllTypesSearchEngine;
import org.key_project.sed.key.ui.util.KeYSEDImages;
import org.key_project.sed.key.ui.util.LogUtil;

/**
 * {@link AbstractLaunchConfigurationTab} implementation for the
 * Symbolic Execution Debugger based on KeY.
 * @author Martin Hentschel
 */
@SuppressWarnings("restriction")
public class KeYLaunchConfigurationTab extends AbstractLaunchConfigurationTab {
    /**
     * Defines the project that contains the type to debug.
     */
    private Text projectText;
    
    /**
     * Defines the type to debug.
     */
    private Text typeText;
    
    /**
     * Defines the method to debug.
     */
    private Text methodText;

    /**
     * {@inheritDoc}
     */
    @Override
    public String getName() {
        return "Main";
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Image getImage() {
        return KeYSEDImages.getImage(KeYSEDImages.LAUNCH_MAIN_TAB_GROUP);
    }
    
    /**
     * {@inheritDoc}
     */
    @Override
    public void createControl(Composite parent) {
        // Root
        Composite rootComposite = new Composite(parent, SWT.NONE);
        setControl(rootComposite);
        rootComposite.setLayout(new GridLayout(1, false));
        // Project
        Group projectGroup = new Group(rootComposite, SWT.NONE);
        projectGroup.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
        projectGroup.setText("Project");
        projectGroup.setLayout(new GridLayout(3, false));
        Label projectLabel = new Label(projectGroup, SWT.NONE);
        projectLabel.setText("&Project name");
        projectText = new Text(projectGroup, SWT.BORDER);
        projectText.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
        projectText.addModifyListener(new ModifyListener() {
            @Override
            public void modifyText(ModifyEvent e) {
                updateLaunchConfigurationDialog();
            }
        });
        Button browseProjectButton = new Button(projectGroup, SWT.PUSH);
        browseProjectButton.setText("B&rowse");
        browseProjectButton.addSelectionListener(new SelectionAdapter() {
            @Override
            public void widgetSelected(SelectionEvent e) {
                browseProject();
            }
        });
        // Java
        Group javaGroup = new Group(rootComposite, SWT.NONE);
        javaGroup.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
        javaGroup.setText("Java");
        javaGroup.setLayout(new GridLayout(3, false));
        Label typeLabel = new Label(javaGroup, SWT.NONE);
        typeLabel.setText("&Type");
        typeText = new Text(javaGroup, SWT.BORDER);
        typeText.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
        typeText.addModifyListener(new ModifyListener() {
            @Override
            public void modifyText(ModifyEvent e) {
                updateLaunchConfigurationDialog();
            }
        });
        Button browseTypeButton = new Button(javaGroup, SWT.PUSH);
        browseTypeButton.setText("&Browse");
        browseTypeButton.addSelectionListener(new SelectionAdapter() {
            @Override
            public void widgetSelected(SelectionEvent e) {
                browseType();
            }
        });
        Label methodLabel = new Label(javaGroup, SWT.NONE);
        methodLabel.setText("&Method");
        methodText = new Text(javaGroup, SWT.BORDER);
        methodText.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
        methodText.addModifyListener(new ModifyListener() {
            @Override
            public void modifyText(ModifyEvent e) {
                updateLaunchConfigurationDialog();
            }
        });
        Button browseMethodButton = new Button(javaGroup, SWT.PUSH);
        browseMethodButton.setText("Bro&wse");
        browseMethodButton.addSelectionListener(new SelectionAdapter() {
            @Override
            public void widgetSelected(SelectionEvent e) {
                browseMethod();
            }
        });
    }

    /**
     * <p>
     * Opens the dialog to select a Java project.
     * </p>
     * <p>
     * The implementation is oriented at {@link AbstractJavaMainTab#handleProjectButtonSelected()}
     * and {@link AbstractJavaMainTab#chooseJavaProject()}.
     * </p>
     */
    public void browseProject() {
        ILabelProvider labelProvider = new JavaElementLabelProvider(JavaElementLabelProvider.SHOW_DEFAULT);
        ElementListSelectionDialog dialog = new ElementListSelectionDialog(getShell(), labelProvider);
        dialog.setTitle("Project Selection"); 
        dialog.setMessage("Select a project to constrain your search."); 
        try {
            dialog.setElements(JDTUtil.getAllJavaProjects());
        }
        catch (JavaModelException jme) {
            LogUtil.getLogger().logError(jme);
        }
        IJavaProject javaProject = getJavaProject();
        if (javaProject != null) {
            dialog.setInitialSelections(new Object[] {javaProject});
        }
        if (dialog.open() == ElementListSelectionDialog.OK) {
            IJavaProject project = (IJavaProject)dialog.getFirstResult();
            projectText.setText(project.getElementName());
        }               
    }
    
    /**
     * Returns the selected {@link IJavaProject} or {@code null} if no one is defined.
     * @return The selected {@link IJavaProject} or {@code null} if no one is defined.
     */
    protected IJavaProject getJavaProject() {
        String projectName = projectText.getText().trim();
        return JDTUtil.getJavaProject(projectName);
    }

    /**
     * <p>
     * Opens the dialog to select a Java type ({@link IType}).
     * </p>
     * <p>
     * The implementation is oriented at {@link JavaMainTab#handleSearchButtonSelected()}.
     * </p>
     */
    public void browseType() {
        try {
            // Search all Java types
            IJavaProject selectedProject = getJavaProject();
            IJavaElement[] elements;
            if (selectedProject != null && selectedProject.exists()) {
                elements = new IJavaElement[] {selectedProject};
            }
            else {
                elements = JDTUtil.getAllJavaProjects();
            }
            if (elements == null) {
                elements = new IJavaElement[] {};
            }
            IJavaSearchScope searchScope = SearchEngine.createJavaSearchScope(elements, IJavaSearchScope.SOURCES);
            AllTypesSearchEngine engine = new AllTypesSearchEngine();
            IType[] types = engine.searchTypes(getLaunchConfigurationDialog(), searchScope);
            // Open selection dialog
            DebugTypeSelectionDialog mmsd = new DebugTypeSelectionDialog(getShell(), types, "Select Type");
            IType selectedType = getType();
            if (selectedType != null) {
                mmsd.setInitialElementSelections(Collections.singletonList(selectedType));
            }
            if (mmsd.open() == DebugTypeSelectionDialog.OK) {
                Object[] results = mmsd.getResult();    
                if (results != null && results.length >= 1 && results[0] instanceof IType) {
                    IType type = (IType)results[0];
                    projectText.setText(type.getJavaProject().getElementName());
                    typeText.setText(type.getFullyQualifiedName());
                }
            }
        }
        catch (Exception e) {
            LogUtil.getLogger().logError(e);
            LogUtil.getLogger().openErrorDialog(getShell(), e);
        }
    }

    /**
     * Returns the currently selected Java type ({@link IType}) or {@code null} if no one is selected.
     * @return The currently selected Java type ({@link IType}) or {@code null} if no one is selected.
     */
    protected IType getType() {
        try {
            String text = typeText.getText().trim();
            if (!text.isEmpty()) {
                IJavaProject project = getJavaProject();
                if (project != null) {
                    return project.findType(text);
                }
                else {
                    return null;
                }
            }
            else {
                return null;
            }
        }
        catch (JavaModelException e) {
            return null;
        }
    }

    /**
     * Opens a dialog to select a Java method ({@link IMethod}).
     */
    public void browseMethod() {
        try {
            // Search all Java types
            IType selectedType = getType();
            IJavaElement[] elements;
            if (selectedType != null && selectedType.exists()) {
                elements = new IJavaElement[] {selectedType};
            }
            else {
                elements = JDTUtil.getAllJavaProjects();
            }
            if (elements == null) {
                elements = new IJavaElement[] {};
            }
            IJavaSearchScope searchScope = SearchEngine.createJavaSearchScope(elements, IJavaSearchScope.SOURCES);
            AllMethodsSearchEngine engine = new AllMethodsSearchEngine();
            IMethod[] methods = engine.searchMethods(getLaunchConfigurationDialog(), searchScope);
            // Open selection dialog
            ILabelProvider labelProvider = new JavaElementLabelProvider(JavaElementLabelProvider.SHOW_DEFAULT);
            ElementListSelectionDialog dialog = new ElementListSelectionDialog(getShell(), labelProvider);
            dialog.setTitle("Method Selection"); 
            dialog.setMessage("Select a method to debug."); 
            dialog.setElements(methods);
            IMethod oldMethod = getMethod();
            if (oldMethod != null) {
                dialog.setInitialSelections(new Object[] {oldMethod});
            }
            if (dialog.open() == ElementListSelectionDialog.OK) {
                IMethod newMethod = (IMethod)dialog.getFirstResult();
                projectText.setText(KeySEDUtil.getProjectValue(newMethod));
                typeText.setText(KeySEDUtil.getTypeValue(newMethod));
                methodText.setText(KeySEDUtil.getMethodValue(newMethod));
            }
        }
        catch (Exception e) {
            LogUtil.getLogger().logError(e);
            LogUtil.getLogger().openErrorDialog(getShell(), e);
        }
    }

    /**
     * Returns the selected Java method ({@link IMethod}) or {@code null}
     * if no one is selected.
     * @return The selected Java method or {@code null} if no one is selected.
     */
    protected IMethod getMethod() {
        try {
            String text = methodText.getText().trim();
            if (!text.isEmpty()) {
                IType type = getType();
                if (type != null) {
                    return (IMethod)JDTUtil.getElementForTextLabel(type.getMethods(), text);
                }
                else {
                    return null;
                }
            }
            else {
                return null;
            }
        }
        catch (JavaModelException e) {
            return null;
        }
    }
    
    /**
     * {@inheritDoc}
     */
    @Override
    public boolean isValid(ILaunchConfiguration launchConfig) {
        boolean valid = super.isValid(launchConfig);
        // Validate Java project
        if (valid) {
            IJavaProject project = getJavaProject();
            if (project == null || !project.exists()) {
                valid = false;
                setErrorMessage("No existing Java project selected.");
            }
        }
        // Validate type
        if (valid) {
            IType type = getType();
            if (type == null || !type.exists()) {
                valid = false;
                setErrorMessage("No existing type selected.");
            }
        }
        // Validate method
        if (valid) {
            IMethod method = getMethod();
            if (method == null || !method.exists()) {
                valid = false;
                setErrorMessage("No existing method selected.");
            }
        }
        if (valid) {
            setErrorMessage(null);
        }
        return valid;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void setDefaults(ILaunchConfigurationWorkingCopy configuration) {
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void initializeFrom(ILaunchConfiguration configuration) {
        try {
            projectText.setText(KeySEDUtil.getProjectValue(configuration));
            typeText.setText(KeySEDUtil.getTypeValue(configuration));
            methodText.setText(KeySEDUtil.getMethodValue(configuration));
        } 
        catch (CoreException e) {
            e.printStackTrace();
        }
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void performApply(ILaunchConfigurationWorkingCopy configuration) {
        configuration.setAttribute(KeySEDUtil.LAUNCH_CONFIGURATION_TYPE_ATTRIBUTE_PROJECT, projectText.getText());
        configuration.setAttribute(KeySEDUtil.LAUNCH_CONFIGURATION_TYPE_ATTRIBUTE_TYPE, typeText.getText());
        configuration.setAttribute(KeySEDUtil.LAUNCH_CONFIGURATION_TYPE_ATTRIBUTE_METHOD, methodText.getText());
    }
}
