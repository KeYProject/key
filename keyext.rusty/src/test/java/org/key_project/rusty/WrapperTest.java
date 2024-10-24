/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty;

import org.key_project.rusty.nast.Wrapper;

import org.junit.jupiter.api.Test;

public class WrapperTest {
    @Test
    void testWrapper() {
        var crate = Wrapper.parse();
        System.out.println(crate);
    }
}
