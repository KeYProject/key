package org.key_project.key4eclipse.starter.ui.property;

import org.eclipse.core.expressions.PropertyTester;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.internal.ui.actions.SelectionConverter;
import org.eclipse.jdt.internal.ui.javaeditor.JavaEditor;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.PlatformUI;
import org.key_project.key4eclipse.starter.ui.Activator;

/**
 * <p>
 * This implementation of {@link PropertyTester} allows to test some properties
 * of the selected elements in a {@link JavaEditor}. 
 * </p>
 * <p>
 * The supported properties are:
 * <ul>
 *    <li><b>selectedElementInstanceOf</b>: to check that current element is an instance of the given class.</li>
 * </ul>
 * </p>
 * <p>
 * Example usage in a command of extension point org.eclipse.ui.handlers:
 * <pre>
 * &lt;and>
 *    &lt;with
 *        variable="activePartId">
 *      &lt;equals
 *             value="org.eclipse.jdt.ui.CompilationUnitEditor">
 *        &lt;/equals>
 *    &lt;/with>
 *    &lt;with
 *          variable="selection">
 *       &lt;and>
 *          &lt;instanceof
 *                value="org.eclipse.jface.text.ITextSelection">
 *          &lt;/instanceof>
 *           &lt;test
 *                   forcePluginActivation="true"
 *                  property="org.key_project.key4eclipse.starter.ui.javaTextSelection.selectedElementInstanceOf"
 *                   value="org.eclipse.jdt.core.IMethod">
 *            &lt;/test>
 *         &lt;/and>
 *      &lt;/with>
 * &lt;/and>
 * </pre>
 * </p>
 * <p>
 * For more information about test expressions have a look at:
 * <ul>
 *    <li><a href="http://help.eclipse.org/indigo/topic/org.eclipse.platform.doc.isv/guide/workbench_cmd_expressions.htm">http://help.eclipse.org/indigo/topic/org.eclipse.platform.doc.isv/guide/workbench_cmd_expressions.htm</a></li>
 *    <li><a href="http://help.eclipse.org/galileo/topic/org.eclipse.platform.doc.isv/reference/api/org/eclipse/core/expressions/package-summary.html">http://help.eclipse.org/galileo/topic/org.eclipse.platform.doc.isv/reference/api/org/eclipse/core/expressions/package-summary.html</a></li>
 * </ul>
 * </p> 
 * @author Martin Hentschel
 */
@SuppressWarnings("restriction")
public class JavaTextSelectionPropertyTester extends PropertyTester {
    /**
     * {@inheritDoc}
     */
    @Override
    public boolean test(Object receiver, String property, Object[] args, Object expectedValue) {
        try {
            boolean result = false;
            if (expectedValue != null) {
                if (receiver instanceof ITextSelection) {
                    ITextSelection textSelection = (ITextSelection)receiver;
                    if ("selectedElementInstanceOf".equals(property)) {
                        IEditorPart editor = PlatformUI.getWorkbench().getActiveWorkbenchWindow().getActivePage().getActiveEditor();
                        if (editor instanceof JavaEditor) {
                            JavaEditor javaEditor = (JavaEditor)editor;
                            IJavaElement element = SelectionConverter.resolveEnclosingElement(javaEditor, textSelection);
                            result = Class.forName(expectedValue.toString()).isInstance(element);
                        }
                    }
                }
            }
            return result;
        } 
        catch (Exception e) {
            e.printStackTrace();
            Activator.getDefault().getLog().log(new Status(IStatus.ERROR, Activator.PLUGIN_ID, e.getMessage(), e));
            return false;
        }
    }
}
