package org.key_project.key4eclipse.starter.core.test.testcase;

import junit.framework.TestCase;

import org.junit.Test;
import org.key_project.key4eclipse.starter.core.util.KeYUtil;

/**
 * Tests for {@link KeYUtil}
 * @author Martin Hentschel
 */
public class KeYUtilTest extends TestCase {
    /**
     * Tests {@link KeYUtil#isFileExtensionSupported(String)}.
     */
    @Test
    public void testIsFileExtensionSupported() {
        assertFalse(KeYUtil.isFileExtensionSupported(null));
        assertFalse(KeYUtil.isFileExtensionSupported("INVALID_EXTENSION"));
        assertTrue(KeYUtil.isFileExtensionSupported(KeYUtil.KEY_FILE_EXTENSION));
        assertTrue(KeYUtil.isFileExtensionSupported(KeYUtil.PROOF_FILE_EXTENSION));
    }
}
