/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.testsuite.basic;

import org.junit.Ignore;
import org.junit.Test;

import static org.junit.Assert.fail;
import static recoder.testsuite.basic.BasicTestsSuite.getConfig;

@Ignore
public class SetupModelTest {
    @Test
    public void testSetupModel() {
        if (getConfig().getProjectSettings().ensureSystemClassesAreInPath()) {
            getConfig().getChangeHistory().updateModel();
        } else {
            fail("Problem with system setup: Cannot locate system classes");
        }
    }
}
