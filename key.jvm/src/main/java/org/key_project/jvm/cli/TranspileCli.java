/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.jvm.cli;

import java.nio.file.Path;
import java.util.List;
import java.util.concurrent.Callable;

import org.key_project.jvm.Transpiler;

import picocli.CommandLine;
import picocli.CommandLine.Command;
import picocli.CommandLine.Option;
import picocli.CommandLine.Parameters;

/**
 * Command-line entry point ({@code org.key_project.jvm.cli.TranspileCli}).
 *
 * <pre>{@code
 *   gradle :key.jvm:run --args="--output build/transpiled path/to/Foo.class"
 * }</pre>
 *
 * @see <a href="https://picocli.info">picocli</a>
 */
@Command(name = "key-jvm-transpile", mixinStandardHelpOptions = true,
    description = "Transpile JVM bytecode (.class/.jar) into compilable Java over the "
        + "jvm.Local runtime used by KeY.")
public class TranspileCli implements Callable<Integer> {

    @Parameters(index = "0..*", description = ".class or .jar files to transpile")
    private List<Path> inputs;

    @Option(names = { "--output", "-o" }, defaultValue = "build/transpiled",
        description = "output directory for the emitted Java source")
    private Path outputDir;

    @Override
    public Integer call() {
        // TODO(M1): wire into ErrorHandling error()/report() (picocli command spec) once the
        // implementation exists.
        final List<Path> emitted = Transpiler.transpile(inputs, outputDir);
        System.out.println("Emitted " + emitted.size() + " source files into " + outputDir);
        return 0;
    }

    public static void main(String[] args) {
        int exitCode = new CommandLine(new TranspileCli()).execute(args);
        System.exit(exitCode);
    }
}
