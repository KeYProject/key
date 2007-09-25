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

    // The plug-in ID
    public static final String PLUGIN_ID = "VisualDebugger";

    // The shared instance
    private static Activator plugin;

    /**
     * The constructor
     */
    public Activator() {
        super();
        plugin = this;
    }

    private IJavaProject project = null;

    private IProject iProject = null;

    private ResourceBundle resourceBundle;

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

    /**
     * Returns the shared instance
     * 
     * @return the shared instance
     */
    public static Activator getDefault() {
        return plugin;
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

    /**
     * Returns an image descriptor for the image file at the given plug-in
     * relative path
     * 
     * @param path
     *            the path
     * @return the image descriptor
     */
    public static ImageDescriptor getImageDescriptor(String path) {
        return imageDescriptorFromPlugin(PLUGIN_ID, path);
    }

    public IJavaProject getProject() {
        return project;
    }

    public void setProject(IJavaProject project) {
        this.project = project;
    }

    public ASTNode getASTNodeForStatementId(SourceElementId id) {
        // IJavaProject project =
        // visualdebugger.Activator.getDefault().getProject();
        IType result = null;
        try {
            result = project.findType(id.getClassName());
        } catch (JavaModelException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }
        if (result == null) {
            System.err.println("ITYPE NOT FOUND: " + id.getClassName());
            return null;
        }
        ICompilationUnit unit = result.getCompilationUnit();
        ASTParser parser = ASTParser.newParser(AST.JLS3);
        parser.setResolveBindings(true);
        parser.setSource(unit);
        CompilationUnit astRoot = (CompilationUnit) parser.createAST(null);

        FindStatementById visitor = new FindStatementById(id);
        astRoot.accept(visitor);
        if (id.isStatement())
            return (visitor.getStatement());
        else
            return visitor.getExpression();

    }

    public Expression getExpression(SourceElementId id) {
        // IJavaProject project =
        // visualdebugger.Activator.getDefault().getProject();
        IType result = null;
        try {
            result = project.findType(id.getClassName());
        } catch (JavaModelException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }
        if (result == null) {
            System.err.println("ITYPE NOT FOUND: " + id.getClassName());
            return null;
        }
        ICompilationUnit unit = result.getCompilationUnit();
        ASTParser parser = ASTParser.newParser(AST.JLS3);
        parser.setResolveBindings(true);
        parser.setSource(unit);
        CompilationUnit astRoot = (CompilationUnit) parser.createAST(null);

        FindStatementById visitor = new FindStatementById(id);
        astRoot.accept(visitor);

        return (visitor.getExpression());

    }

    public ICompilationUnit getCompilationUnit(SourceElementId id) {
        // IJavaProject project =
        // visualdebugger.Activator.getDefault().getProject();
        IType result = null;
        try {
            result = project.findType(id.getClassName());
        } catch (JavaModelException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }
        if (result == null) {
            System.out.println("ITYPE NOT FOUND: " + id.getClassName());
            return null;
        }
        ICompilationUnit unit = result.getCompilationUnit();
        return unit;

    }

    public IProject getIProject() {
        return iProject;
    }

    public void setIProject(IProject project) {
        iProject = project;
    }

}
