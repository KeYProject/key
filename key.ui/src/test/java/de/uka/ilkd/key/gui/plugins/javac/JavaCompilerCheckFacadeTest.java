/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.plugins.javac;

import java.io.File;
import java.util.Collections;
import java.util.concurrent.ExecutionException;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * @author Alexander Weigl
 * @version 1 (29.01.23)
 */
class JavaCompilerCheckFacadeTest {
    @Test
    void compile1() throws ExecutionException, InterruptedException {
        File src = new File("examples/firstTouch/06-BinarySearch/src/").getAbsoluteFile();
        System.out.println(src);
        var promise =
            JavaCompilerCheckFacade.check(null, Collections.emptyList(),
                src.toPath(), new JavacSettings());
        var result = promise.get();
        assertTrue(result.isEmpty());
    }

    @Test
    void compileExternal() throws ExecutionException, InterruptedException {
        File src = new File("examples/firstTouch/06-BinarySearch/src/").getAbsoluteFile();
        System.out.println(src);
        var promise =
            JavaCompilerCheckFacade.checkExternally(null, Collections.emptyList(),
                src.toPath(), new JavacSettings());
        var result = promise.get();
        assertTrue(result.isEmpty());
    }
}
