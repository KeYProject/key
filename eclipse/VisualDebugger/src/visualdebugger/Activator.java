package visualdebugger;

import java.util.MissingResourceException;
import java.util.ResourceBundle;

import org.eclipse.core.resources.IProject;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IType;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.core.dom.*;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.ui.plugin.AbstractUIPlugin;
import org.osgi.framework.BundleContext;

import visualdebugger.views.FindStatementById;
import de.uka.ilkd.key.gui.Main;
import de.uka.ilkd.key.visualdebugger.SourceElementId;

/**
 * The activator class controls the plug-in life cycle
 */
public class Activator extends AbstractUIPlugin {

    // The shared instance
    private static Activator plugin;

    // The plug-in ID
    public static final String PLUGIN_ID = "VisualDebugger";

    /**
     * Returns the shared instance
     * 
     * @return the shared instance
     */
    public static Activator getDefault() {
        return plugin;
    }

    /**
     * Returns an image descriptor for the image file at the given plug-in
     * relative path
     * 
     * @param path
     *                the path
     * @return the image descriptor
     */
    public static ImageDescriptor getImageDescriptor(String path) {
        return imageDescriptorFromPlugin(PLUGIN_ID, path);
    }

    /**
     * Returns the string from the plugin's resource bundle, or 'key' if not
     * found.
     */
    public static String getResourceString(String key) {
        ResourceBundle bundle = getDefault().getResourceBundle();
        try {
            return (bundle != null) ? bundle.getString(key) : key;
        } catch (MissingResourceException e) {
            return key;
        }
    }

    private IProject iProject = null;

    private IJavaProject project = null;

    private ResourceBundle resourceBundle;

    /**
     * The constructor
     */
    public Activator() {
        super();
        plugin = this;
    }

    public ASTNode getASTNodeForStatementId(SourceElementId id) {

        assert id != null && id.isStatement();

        final ICompilationUnit unit = getCompilationUnit(id);
        if (unit == null) {
            return null;
        }

        final FindStatementById visitor = new FindStatementById(id);

        findSourceElement(unit, visitor);

        return visitor.getStatement();
    }

    private void findSourceElement(final ICompilationUnit unit,
            ASTVisitor visitor) {
        final ASTParser parser = ASTParser.newParser(AST.JLS3);
        parser.setResolveBindings(true);
        parser.setSource(unit);
        parser.createAST(null).accept(visitor);
    }

    public ICompilationUnit getCompilationUnit(SourceElementId id) {
        assert id != null;
        
        IType result = null;
        
        try {
            result = project.findType(id.getClassName());
        } catch (JavaModelException e) {
            result = null;
        }
        
        if (result == null) {
            return null;
        }
        
        return result.getCompilationUnit();
    }

    public Expression getExpression(SourceElementId id) {
        assert id != null;
        
        final ICompilationUnit unit = getCompilationUnit(id);
        if (unit == null) {
            return null;
        }

        final FindStatementById visitor = new FindStatementById(id);
        findSourceElement(unit, visitor);

        return visitor.getExpression();
    }

    public IProject getIProject() {
        return iProject;
    }

    public IJavaProject getProject() {
        return project;
    }

    /**
     * Returns the plugin's resource bundle,
     */
    public ResourceBundle getResourceBundle() {
        try {
            if (resourceBundle == null)
                resourceBundle = ResourceBundle
                        .getBundle("visualdebugger.VisualDebuggerResources");
        } catch (MissingResourceException x) {
            resourceBundle = null;
        }
        return resourceBundle;
    }

    public void setIProject(IProject project) {
        iProject = project;
    }

    public void setProject(IJavaProject project) {
        this.project = project;
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.eclipse.ui.plugin.AbstractUIPlugin#start(org.osgi.framework.BundleContext)
     */
    public void start(BundleContext context) throws Exception {
        super.start(context);
        Main.standalone = false;
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.eclipse.ui.plugin.AbstractUIPlugin#stop(org.osgi.framework.BundleContext)
     */
    public void stop(BundleContext context) throws Exception {
        super.stop(context);
        plugin = null;
        resourceBundle = null;
    }

}
