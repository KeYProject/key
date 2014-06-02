/*******************************************************************************
 * Copyright (c) 2014 Karlsruhe Institute of Technology, Germany
 *                    Technical University Darmstadt, Germany
 *                    Chalmers University of Technology, Sweden
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *    Technical University Darmstadt - initial API and implementation and/or initial documentation
 *******************************************************************************/

package org.key_project.key4eclipse.starter.core.expression;

import org.eclipse.core.expressions.PropertyTester;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.internal.ui.actions.SelectionConverter;
import org.eclipse.jdt.internal.ui.javaeditor.JavaEditor;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.swt.widgets.Display;
import org.eclipse.ui.IEditorPart;
import org.key_project.key4eclipse.starter.core.util.LogUtil;
import org.key_project.util.eclipse.WorkbenchUtil;
import org.key_project.util.java.thread.AbstractRunnableWithResult;
import org.key_project.util.java.thread.IRunnableWithResult;

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
    public boolean test(final Object receiver, 
                        final String property, 
                        final Object[] args, 
                        final Object expectedValue) {
        try {
            IRunnableWithResult<Boolean> run = new AbstractRunnableWithResult<Boolean>() {
                @Override
                public void run() {
                    try {
                        boolean result = false;
                        if (expectedValue != null) {
                            if (receiver instanceof ITextSelection) {
                                ITextSelection textSelection = (ITextSelection)receiver;
                                if ("selectedElementInstanceOf".equals(property)) {
                                    IEditorPart editor = WorkbenchUtil.getActiveEditor();
                                    if (editor instanceof JavaEditor) {
                                        JavaEditor javaEditor = (JavaEditor)editor;
                                        IJavaElement element = SelectionConverter.resolveEnclosingElement(javaEditor, textSelection);
                                        result = Class.forName(expectedValue.toString()).isInstance(element);
                                    }
                                }
                            }
                            else if (receiver instanceof JavaEditor) {
                                JavaEditor javaEditor = (JavaEditor)receiver;
                                ISelection selection = javaEditor.getSelectionProvider().getSelection();
                                if (selection instanceof ITextSelection) {
                                    IJavaElement element = SelectionConverter.resolveEnclosingElement(javaEditor, (ITextSelection)selection);
                                    result = Class.forName(expectedValue.toString()).isInstance(element);
                                }
                            }
                        }
                        setResult(result);
                    }
                    catch (Exception e) {
                        setException(e);
                    }
                }
            };
            Display.getDefault().syncExec(run);
            if (run.getException() != null) {
                throw run.getException();
            }
            return run.getResult() != null && run.getResult().booleanValue();
        } 
        catch (Exception e) {
            LogUtil.getLogger().logError(e);
            return false;
        }
    }
}