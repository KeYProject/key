/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.nparser;

import java.io.IOException;
import java.net.URL;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.init.JavaProfile;

import org.junit.jupiter.api.Assumptions;
import org.junit.jupiter.api.Test;

public class ParseLDTsTests {
    @Test
    public void testLDT() throws IOException {
        load("/de/uka/ilkd/key/proof/rules/ldt.key");
    }

    @Test
    public void testSR() throws IOException {
        load("/de/uka/ilkd/key/proof/rules/standardRules.key");
    }


    private void load(String resources) throws IOException {
        Services services = new Services(new JavaProfile());
        services.activateJava(null);
        URL url = getClass().getResource(resources);
        Assumptions.assumeTrue(url != null);
        KeyIO io = new KeyIO(services);
        io.load(url).loadComplete();
    }
}
