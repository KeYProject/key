package org.key_project.key4eclipse.util.test.testcase;

import junit.framework.TestCase;

import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.swt.widgets.Text;
import org.junit.Test;
import org.key_project.key4eclipse.util.eclipse.swt.SWTUtil;

/**
 * Contains tests for {@link SWTUtil}.
 * @author Martin Hentschel
 */
public class SWTUtilTest extends TestCase {
    /**
     * Tests {@link SWTUtil#setText(org.eclipse.swt.widgets.Text, String)}
     */
    @Test
    public void testSetText() {
        // Create UI
        Shell shell = new Shell();
        Text text = new Text(shell, SWT.BORDER);
        // Set "A"
        SWTUtil.setText(text, "A");
        assertEquals("A", text.getText());
        // Set "B"
        SWTUtil.setText(text, "B");
        assertEquals("B", text.getText());
        // Set ""
        SWTUtil.setText(text, "");
        assertEquals("", text.getText());
        // Set "C"
        SWTUtil.setText(text, "C");
        assertEquals("C", text.getText());
        // Set null
        SWTUtil.setText(text, null);
        assertEquals("", text.getText());
    }
}
